-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_thresholdComponent_edge_eq_standardInterp
-- name    : BKAR.Forest.sum_interpolationGap_thresholdComponent_edge_eq_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:34.442799+00:00
-- url     : https://prove2.me/theorems/ad1da4b4-2cf0-4f9b-a54e-ee07bc4d060e
-- title:
--   Forest: sum interpolation Gap threshold Component edge eq standard Interp
-- statement:
--   Layer-cake identity for a BKAR edge value, expressed using threshold
--   components.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L344-L379
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L344-L379

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

theorem BKAR.Forest.sum_interpolationGap_thresholdComponent_edge_eq_standardInterp
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (e : Edge V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if e.right ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) e.left then
          F.interpolationGap u i
        else
          0) = F.standardInterp u e := by sorry
