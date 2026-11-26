-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationLevel_last
-- name    : BKAR.Forest.interpolationLevel_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:28.793346+00:00
-- url     : https://prove2.me/theorems/b63f3eed-694e-4870-b253-44247d57f1a4
-- title:
--   Forest: interpolation Level last
-- statement:
--   The Forest construction uses the interpolation Level last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L114-L122
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L114-L122

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

theorem BKAR.Forest.interpolationLevel_last
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    F.interpolationLevel u
        ⟨(F.interpolationLevels u).card - 1,
          Nat.sub_lt (F.interpolationLevels_card_pos u) Nat.zero_lt_one⟩ = 1 := by sorry
