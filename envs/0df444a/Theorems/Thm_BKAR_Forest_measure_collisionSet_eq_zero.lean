-- Prove2me | Theorems.Thm_BKAR_Forest_measure_collisionSet_eq_zero
-- name    : BKAR.Forest.measure_collisionSet_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:40.650963+00:00
-- url     : https://prove2.me/theorems/f7e2ed08-b28c-4b46-8c2f-b6b0a2e8c66b
-- title:
--   Forest: measure collision Set eq zero
-- statement:
--   The full finite collision locus has measure zero.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L89-L94
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L89-L94

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measure_collisionSet_eq_zero (F : Forest V) :
    (volume : Measure (F.EdgeParam → ℝ)) F.collisionSet = 0 := by sorry
