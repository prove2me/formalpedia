-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_unitCube
-- name    : BKAR.Forest.measurableSet_unitCube
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:53:22.302729+00:00
-- url     : https://prove2.me/theorems/8815035b-1178-41cc-ae36-98e2049a0434
-- title:
--   Forest: measurable Set unit Cube
-- statement:
--   Measurability of the unit parameter cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L245-L248
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L245-L248

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_unitCube (F : Forest V) :
    MeasurableSet F.unitCube := by sorry
