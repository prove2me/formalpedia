-- Prove2me | Theorems.Thm_BKAR_Forest_isCompact_unitCube
-- name    : BKAR.Forest.isCompact_unitCube
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:49:35.035017+00:00
-- url     : https://prove2.me/theorems/5d33045e-b720-558f-8e57-5064bf501943
-- title:
--   Forest: is Compact unit Cube
-- statement:
--   The forest parameter cube is compact.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L251-L254
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L251-L254

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isCompact_unitCube (F : Forest V) :
    IsCompact F.unitCube := by sorry
