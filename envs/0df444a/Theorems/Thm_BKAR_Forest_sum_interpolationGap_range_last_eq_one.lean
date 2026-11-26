-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_last_eq_one
-- name    : BKAR.Forest.sum_interpolationGap_range_last_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:04.364715+00:00
-- url     : https://prove2.me/theorems/ceaea5d8-df22-5ac9-af31-b77c8d490935
-- title:
--   Forest: sum interpolation Gap range last eq one
-- statement:
--   The Forest construction uses the sum interpolation Gap range last eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L328-L338
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L328-L338

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

theorem BKAR.Forest.sum_interpolationGap_range_last_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        F.interpolationGap u i) = 1 := by sorry
