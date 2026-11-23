-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_shapley_apriori_bound
-- name    : Csg.DiscountedCSG.shapley_apriori_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:03:09.005199+00:00
-- url     : https://prove2.me/theorems/dfd850d5-b4d2-494a-ae8c-3ee46ab8e3d1
-- title:
--   Discounted CSG: shapley apriori bound
-- statement:
--   A priori error bound: after `n` iterations from `v`, the distance to `vOpt` is bounded by the
--       first step's movement, shrinking geometrically in `n`. Mirrors `bellman_apriori_bound`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L102-L104
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L102-L104

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.shapley_apriori_bound (v : S → ℝ) (n : ℕ) :
    dist (D.shapley^[n] v) D.vOpt ≤ dist v (D.shapley v) * (D.lNN : ℝ) ^ n / (1 - D.lNN) := by sorry
