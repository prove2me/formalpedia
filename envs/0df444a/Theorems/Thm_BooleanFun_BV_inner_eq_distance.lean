-- Prove2me | Theorems.Thm_BooleanFun_BV_inner_eq_distance
-- name    : BooleanFun.BV.inner_eq_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:51.103938+00:00
-- url     : https://prove2.me/theorems/0cc1244e-3d73-4f18-af34-ea2088bc9eb2
-- title:
--   BV: inner eq distance
-- statement:
--   The BV construction uses the inner eq distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L267-L275
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L267-L275

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.inner_eq_distance (hbv : BooleanValued f) (hbvg : BooleanValued g) :
    ⟪f, g⟫ = 1-2 * distance f g := by sorry
