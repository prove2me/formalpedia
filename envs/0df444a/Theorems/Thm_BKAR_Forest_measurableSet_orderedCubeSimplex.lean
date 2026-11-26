-- Prove2me | Theorems.Thm_BKAR_Forest_measurableSet_orderedCubeSimplex
-- name    : BKAR.Forest.measurableSet_orderedCubeSimplex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:56:28.093845+00:00
-- url     : https://prove2.me/theorems/b0f71747-7cac-535f-ae6a-78a164fc29cd
-- title:
--   Forest: measurable Set ordered Cube Simplex
-- statement:
--   Each closed ordered cube sector is measurable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L280-L285
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L280-L285

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurableSet_orderedCubeSimplex
    (F : Forest V) (order : List (Edge V)) :
    MeasurableSet (F.orderedCubeSimplex order) := by sorry
