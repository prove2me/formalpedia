-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationLevels_min_eq_zero
-- name    : BKAR.Forest.interpolationLevels_min_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:22:27.84021+00:00
-- url     : https://prove2.me/theorems/f4848f04-3eed-4284-8fa9-f93ff90fd3c0
-- title:
--   Forest: interpolation Levels min eq zero
-- statement:
--   The Forest construction uses the interpolation Levels min eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L78-L87
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L78-L87

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

theorem BKAR.Forest.interpolationLevels_min_eq_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (F.interpolationLevels u).min'
        ⟨0, F.zero_mem_interpolationLevels u⟩ = 0 := by sorry
