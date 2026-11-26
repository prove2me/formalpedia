-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationGap_nonneg
-- name    : BKAR.Forest.interpolationGap_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:56.074659+00:00
-- url     : https://prove2.me/theorems/3971cf99-5720-5018-8381-aa47c2af617a
-- title:
--   Forest: interpolation Gap nonneg
-- statement:
--   The Forest construction uses the interpolation Gap nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L166-L176
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L166-L176

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

theorem BKAR.Forest.interpolationGap_nonneg
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    0 ≤ F.interpolationGap u i := by sorry
