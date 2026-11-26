-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationLevel_zero
-- name    : BKAR.Forest.interpolationLevel_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:20:48.502217+00:00
-- url     : https://prove2.me/theorems/08c4d4c6-6e9e-418b-8795-b0fed2d35a07
-- title:
--   Forest: interpolation Level zero
-- statement:
--   The Forest construction uses the interpolation Level zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L105-L112
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L105-L112

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

theorem BKAR.Forest.interpolationLevel_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    F.interpolationLevel u
        ⟨0, F.interpolationLevels_card_pos u⟩ = 0 := by sorry
