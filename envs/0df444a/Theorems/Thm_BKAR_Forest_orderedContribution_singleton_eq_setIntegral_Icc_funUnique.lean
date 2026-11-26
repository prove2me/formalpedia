-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_singleton_eq_setIntegral_Icc_funUnique
-- name    : BKAR.Forest.orderedContribution_singleton_eq_setIntegral_Icc_funUnique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:45.069864+00:00
-- url     : https://prove2.me/theorems/0f3508ab-a7f4-4357-ad3f-56c7db8f8f24
-- title:
--   Forest: ordered Contribution singleton eq set Integral Icc fun Unique
-- statement:
--   First step of the simplex-sector conversion for one edge: the recursive
--   ordered contribution is the
--   ordinary set integral over the one-dimensional simplex coordinate. The
--   remaining singleton sector bridge is exactly the `funUnique` measure-preserving
--   identification of that coordinate with the one-edge cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L129-L160
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean#L129-L160

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_singleton_eq_setIntegral_Icc_funUnique
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e})
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution [e] ρ =
      ∫ t in Set.Icc (0 : ℝ) 1,
        mixedPartialList [e].reverse ρ
          (F.standardInterp
            ((@MeasurableEquiv.funUnique F.EdgeParam ℝ
              (F.uniqueEdgeParamOfEdgesSingleton hedges) inferInstance).symm t)) := by sorry
