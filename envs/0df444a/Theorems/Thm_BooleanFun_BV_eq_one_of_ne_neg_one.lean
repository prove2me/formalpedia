-- Prove2me | Theorems.Thm_BooleanFun_BV_eq_one_of_ne_neg_one
-- name    : BooleanFun.BV.eq_one_of_ne_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:11:18.928462+00:00
-- url     : https://prove2.me/theorems/0607e914-a3a9-4ec3-8826-4f4f91c49725
-- title:
--   BV: eq one of ne neg one
-- statement:
--   The BV construction uses the eq one of ne neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L58-L59
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L58-L59

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.eq_one_of_ne_neg_one (hbv : BooleanValued f) (h' : f x ≠ -1) : f x = 1 := by sorry
