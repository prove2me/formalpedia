-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_le_eq_of_mem_interpolationLevels
-- name    : BKAR.Forest.sum_interpolationGap_le_eq_of_mem_interpolationLevels
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:05.310954+00:00
-- url     : https://prove2.me/theorems/0669fe90-e2a9-593f-90ab-022e6cee6192
-- title:
--   Forest: sum interpolation Gap le eq of mem interpolation Levels
-- statement:
--   The Forest construction uses the sum interpolation Gap le eq of mem interpolation Levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L262-L326
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L262-L326

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

theorem BKAR.Forest.sum_interpolationGap_le_eq_of_mem_interpolationLevels
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {x : ℝ} (hx : x ∈ F.interpolationLevels u) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if F.interpolationLayerThreshold u i ≤ x then
          F.interpolationGap u i
        else
          0) = x := by sorry
