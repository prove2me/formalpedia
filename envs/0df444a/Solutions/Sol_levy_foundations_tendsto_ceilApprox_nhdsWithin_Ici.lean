-- Prove2me | solution 1 for levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:44:00.222191+00:00
-- url     : https://prove2.me/submissions/745f0dd5-773c-4098-8a33-7fe1dcd6f04d

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_ceilApprox
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_DensityExtension_tendsto_ceilApprox_nhdsWithin_Ici

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

theorem solution (t : ℝ≥0) :
    Tendsto (LevyFoundations.DensityExtension.ceilApprox t) atTop (𝓝[≥] t) := by
  exact DensityExtension.tendsto_ceilApprox_nhdsWithin_Ici t
