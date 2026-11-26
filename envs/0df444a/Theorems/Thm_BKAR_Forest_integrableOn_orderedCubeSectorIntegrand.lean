-- Prove2me | Theorems.Thm_BKAR_Forest_integrableOn_orderedCubeSectorIntegrand
-- name    : BKAR.Forest.integrableOn_orderedCubeSectorIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:57:16.575448+00:00
-- url     : https://prove2.me/theorems/fea2118f-c280-428f-b150-c8f9d0219854
-- title:
--   Forest: integrable On ordered Cube Sector Integrand
-- statement:
--   Integrability of an ordered-sector integrand on the forest parameter cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L83-L91
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L83-L91

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

theorem BKAR.Forest.integrableOn_orderedCubeSectorIntegrand
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        mixedPartialList order.reverse ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) := by sorry
