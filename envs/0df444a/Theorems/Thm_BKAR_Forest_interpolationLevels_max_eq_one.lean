-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationLevels_max_eq_one
-- name    : BKAR.Forest.interpolationLevels_max_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:22:29.59593+00:00
-- url     : https://prove2.me/theorems/f9ad04cc-f96b-44dd-b364-a43cb7b0a3d1
-- title:
--   Forest: interpolation Levels max eq one
-- statement:
--   The Forest construction uses the interpolation Levels max eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L89-L98
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L89-L98

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

theorem BKAR.Forest.interpolationLevels_max_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (F.interpolationLevels u).max'
        ⟨1, F.one_mem_interpolationLevels u⟩ = 1 := by sorry
