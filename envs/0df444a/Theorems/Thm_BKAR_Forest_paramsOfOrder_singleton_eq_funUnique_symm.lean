-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_singleton_eq_funUnique_symm
-- name    : BKAR.Forest.paramsOfOrder_singleton_eq_funUnique_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:11.260426+00:00
-- url     : https://prove2.me/theorems/0a58d327-7c9f-4257-9f3f-ba6d1c279598
-- title:
--   Forest: params Of Order singleton eq fun Unique symm
-- statement:
--   The Forest construction uses the params Of Order singleton eq fun Unique symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L45-L70
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L45-L70

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

theorem BKAR.Forest.paramsOfOrder_singleton_eq_funUnique_symm
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e})
    (t : ℝ) :
    F.paramsOfOrder [e] [t] =
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance).symm t := by sorry
