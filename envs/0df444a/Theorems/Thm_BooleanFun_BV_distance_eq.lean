-- Prove2me | Theorems.Thm_BooleanFun_BV_distance_eq
-- name    : BooleanFun.BV.distance_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:44.685207+00:00
-- url     : https://prove2.me/theorems/7843e56e-ade5-4dd9-9923-3d30cfd618f8
-- title:
--   BV: distance eq
-- statement:
--   The BV construction uses the distance eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L263-L265
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L263-L265

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.distance_eq (hbv : BooleanValued f) (hbvg : BooleanValued g) :
    distance f g = 𝐄 (fun x ↦ (1/2) * (1-(f x) * (g x))) := by sorry
