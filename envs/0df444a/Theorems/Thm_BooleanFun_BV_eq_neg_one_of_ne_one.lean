-- Prove2me | Theorems.Thm_BooleanFun_BV_eq_neg_one_of_ne_one
-- name    : BooleanFun.BV.eq_neg_one_of_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:12.504227+00:00
-- url     : https://prove2.me/theorems/ed5ccac5-c5f1-4754-b421-8f85efd2b3a5
-- title:
--   BV: eq neg one of ne one
-- statement:
--   The BV construction uses the eq neg one of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L55-L56
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L55-L56

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.eq_neg_one_of_ne_one (hbv : BooleanValued f) (h' : f x ≠ 1) : f x = -1 := by sorry
