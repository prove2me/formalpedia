-- Prove2me | Theorems.Thm_BKAR_Forest_measurable_paramValue
-- name    : BKAR.Forest.measurable_paramValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:52:29.907581+00:00
-- url     : https://prove2.me/theorems/09bba18d-7be9-4baf-a847-cdcac0cecea4
-- title:
--   Forest: measurable param Value
-- statement:
--   Coordinate lookup as a measurable function on the forest parameter cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L226-L242
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasurePartition.lean#L226-L242

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurable_paramValue (F : Forest V) (e : Edge V) :
    Measurable fun u : F.EdgeParam → ℝ => F.paramValue u e := by sorry
