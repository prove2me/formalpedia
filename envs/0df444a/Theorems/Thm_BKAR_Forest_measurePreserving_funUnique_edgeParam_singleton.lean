-- Prove2me | Theorems.Thm_BKAR_Forest_measurePreserving_funUnique_edgeParam_singleton
-- name    : BKAR.Forest.measurePreserving_funUnique_edgeParam_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:08:09.868399+00:00
-- url     : https://prove2.me/theorems/3efed1de-181e-4968-9e2e-8da6973e16b7
-- title:
--   Forest: measure Preserving fun Unique edge Param singleton
-- statement:
--   The Forest construction uses the measure Preserving fun Unique edge Param singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L100-L108
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L100-L108

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.measurePreserving_funUnique_edgeParam_singleton
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    MeasurePreserving
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance)
      (volume : Measure (F.EdgeParam → ℝ)) (volume : Measure ℝ) := by sorry
