-- Prove2me | Theorems.Thm_BKAR_Forest_integrableOn_cubeContributionIntegrand
-- name    : BKAR.Forest.integrableOn_cubeContributionIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:01.182539+00:00
-- url     : https://prove2.me/theorems/8b77e026-98f6-441a-9d29-fc0d956d0d15
-- title:
--   Forest: integrable On cube Contribution Integrand
-- statement:
--   Integrability of the usual unordered cube integrand on the forest parameter cube.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L40-L48
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L40-L48

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integrableOn_cubeContributionIntegrand
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    IntegrableOn
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u))
      F.unitCube (volume : Measure (F.EdgeParam → ℝ)) := by sorry
