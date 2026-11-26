-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_mem_interpolationLevels
-- name    : BKAR.Forest.standardInterp_mem_interpolationLevels
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:22:10.659956+00:00
-- url     : https://prove2.me/theorems/62112fe9-baa1-5702-97a1-dc39ef951465
-- title:
--   Forest: standard Interp mem interpolation Levels
-- statement:
--   The Forest construction uses the standard Interp mem interpolation Levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L46-L50
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ThresholdLayerCake.lean#L46-L50

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

theorem BKAR.Forest.standardInterp_mem_interpolationLevels
    (F : Forest V) (u : F.EdgeParam → ℝ) (e : Edge V) :
    F.standardInterp u e ∈ F.interpolationLevels u := by sorry
