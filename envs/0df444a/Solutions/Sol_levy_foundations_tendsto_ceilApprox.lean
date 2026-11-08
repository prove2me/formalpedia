-- Prove2me | solution 1 for levy_foundations_tendsto_ceilApprox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:44:08.68239+00:00
-- url     : https://prove2.me/submissions/d3e21052-66e8-4073-9f7e-c781f38f60f9

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_ceilApprox
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_DensityExtension_tendsto_ceilApprox

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

theorem solution (t : ℝ≥0) :
    Tendsto (LevyFoundations.DensityExtension.ceilApprox t) atTop (𝓝 t) := by
  exact DensityExtension.tendsto_ceilApprox t
