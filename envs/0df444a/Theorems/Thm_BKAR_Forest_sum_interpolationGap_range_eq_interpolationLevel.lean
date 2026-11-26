-- Prove2me | Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_eq_interpolationLevel
-- name    : BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:23:54.306501+00:00
-- url     : https://prove2.me/theorems/8e79a7d6-39ba-583d-a214-a0c100266883
-- title:
--   Forest: sum interpolation Gap range eq interpolation Level
-- statement:
--   The Forest construction uses the sum interpolation Gap range eq interpolation Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L215-L250
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L215-L250

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

theorem BKAR.Forest.sum_interpolationGap_range_eq_interpolationLevel
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ -
        F.interpolationLevel u
          ⟨0, F.interpolationLevels_card_pos u⟩ := by sorry
