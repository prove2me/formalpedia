-- Prove2me | Theorems.Thm_BKAR_Forest_interpolationGap_of_lt
-- name    : BKAR.Forest.interpolationGap_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:34.958553+00:00
-- url     : https://prove2.me/theorems/06c9720e-6d90-5ae0-a776-32dba3139f8c
-- title:
--   Forest: interpolation Gap of lt
-- statement:
--   The Forest construction uses the interpolation Gap of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L154-L164
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L154-L164

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

theorem BKAR.Forest.interpolationGap_of_lt
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationGap u i =
      F.interpolationLevel u
        ⟨i + 1, by
          omega⟩ -
        F.interpolationLevel u
          ⟨i, by
            omega⟩ := by sorry
