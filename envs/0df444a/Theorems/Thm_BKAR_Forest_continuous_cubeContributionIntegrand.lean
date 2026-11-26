-- Prove2me | Theorems.Thm_BKAR_Forest_continuous_cubeContributionIntegrand
-- name    : BKAR.Forest.continuous_cubeContributionIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:04:26.81439+00:00
-- url     : https://prove2.me/theorems/f98045c3-e93f-5c66-aa46-072693f89d81
-- title:
--   Forest: continuous cube Contribution Integrand
-- statement:
--   Continuity of the usual unordered cube integrand under the BKAR smoothness hypothesis.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L25-L37
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean#L25-L37

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.continuous_cubeContributionIntegrand
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Continuous
      (fun u : F.EdgeParam → ℝ =>
        F.mixedPartial ρ (F.standardInterp u)) := by sorry
