/*
** $Id: ltm.c,v 2.38.1.1 2017/04/19 17:39:34 roberto Exp $
** Tag methods
** See Copyright Notice in lua.h
*/

#define ltm_c
#define LUA_CORE

#include "lprefix.h"


#include <string.h>

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"
#include "lvm.h"


static const char udatatypename[] = "userdata";

static const char *const luaT_typenames[LUA_TOTALTAGS] = {
  "no value",
  "nil", "boolean", udatatypename, "number",
  "string", "table", "function", udatatypename, "thread", "proxy",
  "proto" /* this last case is used for tests only */
};

static const char *const luaT_eventname[] = {  /* ORDER TM */
  "__index", "__newindex",
  "__gc", "__mode", "__len", "__eq",
  "__add", "__sub", "__mul", "__mod", "__pow",
  "__div", "__idiv",
  "__band", "__bor", "__bxor", "__shl", "__shr",
  "__unm", "__bnot", "__lt", "__le",
  "__concat", "__call"
};


void luaT_init (lua_State *L) {
  int i;
  for (i=0; i<TM_N; i++) {
    G(L)->tmname[i] = luaS_new(L, luaT_eventname[i]);
    luaC_fix(L, obj2gco(G(L)->tmname[i]));  /* never collect these names */
  }
  for (i=0; i<LUA_TOTALTAGS; i++) {
    G(L)->tpname[i] = luaS_new(L, luaT_typenames[i]);
    luaC_fix(L, obj2gco(G(L)->tpname[i]));  /* never collect these names */
  }
}


/*
** function to be used with macro "fasttm": optimized for absence of
** tag methods
*/
const TValue *luaT_gettm (lua_State *L, Table *events,
                                        TMS event,
                                        TString *ename) {
  const TValue *tm = luaH_getshortstr(L, events, ename);
  lua_assert(event <= TM_EQ);
  if (ttisnil(tm)) {  /* no tag method? */
    events->flags |= cast_byte(1u<<event);  /* cache this fact */
    return NULL;
  }
  else return tm;
}


const TValue *luaT_gettmbyobj (lua_State *L, const TValue *o, TMS event) {
  Table *mt;
  switch (ttnov(o)) {
    case LUA_TTABLE:
      mt = hvalue(o)->metatable;
      break;
    case LUA_TUSERDATA:
      mt = uvalue(o)->metatable;
      break;
    case LUA_TPROXY:
      mt = pxvalue(o)->metatable;
      break;
    default:
      mt = NULL;
      break;
  }
  return (mt ? luaH_getshortstr(L, mt, G(L)->tmname[event])
             : luaO_nilobject(L));
}


/*
** Return the name of the type of an object. For tables and userdata
** with metatable, use their '__type' metafield, if present.
*/
const char *luaT_objtypename (lua_State *L, const TValue *o) {
  Table *mt;
  if ((ttistable(o) && (mt = hvalue(o)->metatable) != NULL) ||
      (ttisfulluserdata(o) && (mt = uvalue(o)->metatable) != NULL) ||
      (ttisproxy(o) && (mt = pxvalue(o)->metatable) != NULL)) {
    const TValue *name = luaH_getshortstr(L, mt, luaS_new(L, "__type"));
    if (ttisstring(name))  /* is '__type' a string? */
      return getstr(tsvalue(name));  /* use it as type name */
  }
  return getstr(G(L)->tpname[ttnov(o) + 1]);  /* else use standard type name */
}


#define checkflag(f, o) (((f) & (o)) != 0)

void luaT_callTM (lua_State *L, const TValue *f, const TValue *p1,
                  const TValue *p2, TValue *p3, int flags) {
  int hasres = checkflag(flags, LUA_HASRES_META);
  int binop = checkflag(flags, LUA_BINOP_META);
  int isother = checkflag(flags, LUA_ISOTHER_META);
  ptrdiff_t result = savestack(L, p3);
  StkId func = L->top;
  if (ttisproxy(p1) || ttisproxy(p2)) {
    const TValue *tmp;
    if (!isother) {
      tmp = p1;
      if (ttisproxy(p1)) {
        tmp = &pxvalue(p1)->value;
        if (ttisproxy(p2) && binop &&
            pxvalue(p1) == pxvalue(p2))  /* special case: object is same */
          p2 = &pxvalue(p2)->value;
      }
      p1 = tmp;
    }
    else {
      tmp = p2;
      if (ttisproxy(p2)) {
        tmp = &pxvalue(p2)->value;
        if (ttisproxy(p1) && binop &&
            pxvalue(p1) == pxvalue(p2))  /* special case: object is same */
          p1 = &pxvalue(p1)->value;
      }
      p2 = tmp;
    }
  }
  if (binop) {
    const TValue *po = (!isother) ? p1 : p2;  /* owner of call */
    setobj2s(L, func, f);  /* push function (assume EXTRA_STACK) */
    setobj2s(L, func + 1, po);  /* 1st argument (self) */
    setobj2s(L, func + 2, p1);  /* 2nd argument (lhs) */
    setobj2s(L, func + 3, p2);  /* 3rd argument (rhs) */
    L->top += 4;
  }
  else {
    setobj2s(L, func, f);  /* push function (assume EXTRA_STACK) */
    setobj2s(L, func + 1, p1);  /* 1st argument */
    setobj2s(L, func + 2, p2);  /* 2nd argument */
    L->top += 3;
  }
  if (!hasres)  /* no result? 'p3' is third argument */
    setobj2s(L, L->top++, p3);  /* 3rd argument */
  /* metamethod may yield only when called from Lua code */
  if (isLua(L->ci))
    luaD_call(L, func, hasres);
  else
    luaD_callnoyield(L, func, hasres);
  if (hasres) {  /* if has result, move it to its place */
    p3 = restorestack(L, result);
    setobjs2s(L, p3, --L->top);
  }
}


int luaT_callbinTM (lua_State *L, const TValue *p1, const TValue *p2,
                    StkId res, TMS event) {
  int flags = LUA_HASRES_META | LUA_BINOP_META;
  const TValue *tm = luaT_gettmbyobj(L, p1, event);  /* try first operand */
  if (ttisnil(tm)) {
    tm = luaT_gettmbyobj(L, p2, event);  /* try second operand */
    if (!ttisnil(tm)) flags |= LUA_ISOTHER_META;
  }
  if (ttisnil(tm)) return 0;
  luaT_callTM(L, tm, p1, p2, res, flags);
  return 1;
}


void luaT_trybinTM (lua_State *L, const TValue *p1, const TValue *p2,
                    StkId res, TMS event) {
  if (!luaT_callbinTM(L, p1, p2, res, event)) {
    switch (event) {
      case TM_CONCAT:
        luaG_concaterror(L, p1, p2);
      /* call never returns, but to avoid warnings: *//* FALLTHROUGH */
      case TM_BAND: case TM_BOR: case TM_BXOR:
      case TM_SHL: case TM_SHR: case TM_BNOT: {
        lua_Number dummy;
        if (tonumber(p1, &dummy) && tonumber(p2, &dummy))
          luaG_tointerror(L, p1, p2);
        else
          luaG_opinterror(L, p1, p2, "perform bitwise operation on");
      }
      /* calls never return, but to avoid warnings: *//* FALLTHROUGH */
      default:
        luaG_opinterror(L, p1, p2, "perform arithmetic on");
    }
  }
}


int luaT_callorderTM (lua_State *L, const TValue *p1, const TValue *p2,
                      TMS event) {
  if (!luaT_callbinTM(L, p1, p2, L->top, event))
    return -1;  /* no metamethod */
  else
    return !l_isfalse(L->top);
}

