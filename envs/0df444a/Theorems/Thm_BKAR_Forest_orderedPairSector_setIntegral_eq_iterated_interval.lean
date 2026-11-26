-- Prove2me | Theorems.Thm_BKAR_Forest_orderedPairSector_setIntegral_eq_iterated_interval
-- name    : BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:08:47.735777+00:00
-- url     : https://prove2.me/theorems/58408b17-35df-5da2-adab-aa8f8659594f
-- title:
--   Forest: ordered Pair Sector set Integral eq iterated interval
-- statement:
--   The Forest construction uses the ordered Pair Sector set Integral eq iterated interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L130-L147
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L130-L147

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_interval
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by sorry
