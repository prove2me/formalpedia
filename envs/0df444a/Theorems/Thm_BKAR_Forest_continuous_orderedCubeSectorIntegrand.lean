-- Prove2me | Theorems.Thm_BKAR_Forest_continuous_orderedCubeSectorIntegrand
-- name    : BKAR.Forest.continuous_orderedCubeSectorIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:06:07.245051+00:00
-- url     : https://prove2.me/theorems/82aa4581-7447-54d7-b7f1-2a369f7bd1f2
-- title:
--   Forest: continuous ordered Cube Sector Integrand
-- statement:
--   Continuity of an ordered-sector integrand under the BKAR smoothness hypothesis.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L73-L80
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L73-L80

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.continuous_orderedCubeSectorIntegrand
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u)) := by sorry
