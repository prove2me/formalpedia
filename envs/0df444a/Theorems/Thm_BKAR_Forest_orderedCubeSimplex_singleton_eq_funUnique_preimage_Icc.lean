-- Prove2me | Theorems.Thm_BKAR_Forest_orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
-- name    : BKAR.Forest.orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:14.730802+00:00
-- url     : https://prove2.me/theorems/840de6e1-7f2e-4ecb-901d-d05ab5dd3bea
-- title:
--   Forest: ordered Cube Simplex singleton eq fun Unique preimage Icc
-- statement:
--   The Forest construction uses the ordered Cube Simplex singleton eq fun Unique preimage Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L72-L98
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L72-L98

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

theorem BKAR.Forest.orderedCubeSimplex_singleton_eq_funUnique_preimage_Icc
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    F.orderedCubeSimplex [e] =
      (@MeasurableEquiv.funUnique F.EdgeParam ℝ
        (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance) ⁻¹'
        Set.Icc (0 : ℝ) 1 := by sorry
