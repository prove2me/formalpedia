-- Prove2me | Theorems.Thm_BooleanFun_BV_oneOn_ne_of_one_or_neg_one
-- name    : BooleanFun.BV.oneOn_ne_of_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:37.088508+00:00
-- url     : https://prove2.me/theorems/3603863c-cf11-4d25-95d7-36beae1b8933
-- title:
--   BV: one On ne of one or neg one
-- statement:
--   The BV construction uses the one On ne of one or neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L259-L261
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L259-L261

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.oneOn_ne_of_one_or_neg_one {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1):
    oneOn (x ≠ y) = (1/2) * (1-x * y) := by sorry
