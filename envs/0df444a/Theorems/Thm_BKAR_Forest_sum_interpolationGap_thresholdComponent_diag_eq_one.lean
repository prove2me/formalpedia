-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_thresholdComponent_diag_eq_one
-- name    : BKAR.Forest.sum_interpolationGap_thresholdComponent_diag_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:47.621+00:00
-- url     : https://prove2.me/theorems/4ba95af3-1ecc-4364-97ab-266f9e80b083
-- title:
--   Forest: sum interpolation Gap threshold Component diag eq one
-- statement:
--   Diagonal layer-cake identity: every threshold component contains its base point.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L382-L409
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L382-L409

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Forest.sum_interpolationGap_thresholdComponent_diag_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (z : V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if z ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) z then
          F.interpolationGap u i
        else
          0) = 1 := by sorry
