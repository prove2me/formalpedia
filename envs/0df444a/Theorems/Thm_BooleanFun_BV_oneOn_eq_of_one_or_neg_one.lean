-- Prove2me | Theorems.Thm_BooleanFun_BV_oneOn_eq_of_one_or_neg_one
-- name    : BooleanFun.BV.oneOn_eq_of_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:33.390277+00:00
-- url     : https://prove2.me/theorems/6e00c3f1-be74-4bde-9419-9814ca396a28
-- title:
--   BV: one On eq of one or neg one
-- statement:
--   The BV construction uses the one On eq of one or neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L255-L257
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L255-L257

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.oneOn_eq_of_one_or_neg_one {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1):
    oneOn (x = y) = (1/2) * (1 + x * y) := by sorry
