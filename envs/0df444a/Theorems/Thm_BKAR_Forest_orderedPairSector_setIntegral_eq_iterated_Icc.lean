-- Prove2me | Theorems.Thm_BKAR_Forest_orderedPairSector_setIntegral_eq_iterated_Icc
-- name    : BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:09:21.53523+00:00
-- url     : https://prove2.me/theorems/db52cbed-2543-476d-83cb-7643c184c9cb
-- title:
--   Forest: ordered Pair Sector set Integral eq iterated Icc
-- statement:
--   The Forest construction uses the ordered Pair Sector set Integral eq iterated Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L80-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean#L80-L127

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedPairSector_setIntegral_eq_iterated_Icc
    (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f orderedPairSector) :
    ∫ z in orderedPairSector, f z =
      ∫ x in Set.Icc (0 : ℝ) 1, ∫ y in Set.Icc (0 : ℝ) x, f (x, y) := by sorry
