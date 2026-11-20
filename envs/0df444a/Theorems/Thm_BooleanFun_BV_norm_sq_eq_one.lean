-- Prove2me | Theorems.Thm_BooleanFun_BV_norm_sq_eq_one
-- name    : BooleanFun.BV.norm_sq_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:04:49.985436+00:00
-- url     : https://prove2.me/theorems/e299bafe-aa93-4bb5-941a-8d8e0c808537
-- title:
--   BV: norm sq eq one
-- statement:
--   The BV construction uses the norm sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L39-L49
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L39-L49

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.norm_sq_eq_one (hbv : BooleanValued f):
    ‖f‖^2 = 1 := by sorry
