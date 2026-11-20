-- Prove2me | Theorems.Thm_BooleanFun_BV_acceptanceProbabilityBLR_eq
-- name    : BooleanFun.BV.acceptanceProbabilityBLR_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:51.737926+00:00
-- url     : https://prove2.me/theorems/2b82bfb7-c9d3-4f14-a3a1-419d0b3656a9
-- title:
--   BV: acceptance Probability BLR eq
-- statement:
--   The BV construction uses the acceptance Probability BLR eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L290-L296
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L290-L296

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.acceptanceProbabilityBLR_eq (hbv : BooleanValued f) : acceptanceProbabilityBLR f =
    (𝐄 <| fun x ↦ 𝐄 <| fun y ↦ (1/2) * (1 + (f x) * (f y) * (f (x + y)))) := by sorry
