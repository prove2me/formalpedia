-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_eq_interpolationLevel_of_zero
-- name    : BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel_of_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:20:54.675846+00:00
-- url     : https://prove2.me/theorems/e9c7925a-d47f-47c6-910b-5b7cf82641dc
-- title:
--   Forest: sum interpolation Gap range eq interpolation Level of zero
-- statement:
--   The Forest construction uses the sum interpolation Gap range eq interpolation Level of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L252-L260
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L252-L260

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

theorem BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel_of_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ := by sorry
