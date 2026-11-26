-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationLayerThreshold_pos
-- name    : BKAR.Forest.interpolationLayerThreshold_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:22:33.447194+00:00
-- url     : https://prove2.me/theorems/09056243-3c1a-452d-a157-792ffbcba64b
-- title:
--   Forest: interpolation Layer Threshold pos
-- statement:
--   The Forest construction uses the interpolation Layer Threshold pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L178-L191
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L178-L191

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

theorem BKAR.Forest.interpolationLayerThreshold_pos
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {i : ℕ} (hi : i < (F.interpolationLevels u).card - 1) :
    0 < F.interpolationLayerThreshold u i := by sorry
