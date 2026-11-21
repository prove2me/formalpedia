-- Prove2me | Theorems.Thm_Eidos_Ergo_error_not_accepted
-- name    : Eidos.Ergo.error_not_accepted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:36.20673+00:00
-- url     : https://prove2.me/theorems/85f36581-4f88-4545-915b-dca303d40ad1
-- title:
--   Ergo: error not accepted
-- statement:
--   The Ergo construction uses the error not accepted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Expr.lean#L45-L47
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Expr.lean#L45-L47

import Definitions.Def_Eidos_Ergo_Context
import Definitions.Def_Eidos_Ergo_Expr
set_option autoImplicit false
open Eidos Eidos.Ergo

theorem Eidos.Ergo.error_not_accepted (script : BoolExpr) (ctx : Context) (err : EvalError)
    (h : script.eval ctx = .error err) : ¬ Accepts script ctx := by sorry
