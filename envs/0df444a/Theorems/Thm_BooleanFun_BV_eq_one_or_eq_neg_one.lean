-- Prove2me | Theorems.Thm_BooleanFun_BV_eq_one_or_eq_neg_one
-- name    : BooleanFun.BV.eq_one_or_eq_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:10:49.56417+00:00
-- url     : https://prove2.me/theorems/4fd8c72d-d1bd-4430-9ddb-71dc46431c23
-- title:
--   BV: eq one or eq neg one
-- statement:
--   The BV construction uses the eq one or eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L36-L37
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L36-L37

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.eq_one_or_eq_neg_one (hbv : BooleanValued f) : ∀ x, f x = 1 ∨ f x = -1 := by sorry
