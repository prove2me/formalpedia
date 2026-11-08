-- Prove2me | solution 1 for levy_foundations_ceilApprox_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:44:04.759183+00:00
-- url     : https://prove2.me/submissions/5c81f047-5845-460f-af0e-abe5d41363da

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_ceilApprox
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_DensityExtension_ceilApprox_coe

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

theorem solution (t : ℝ≥0) (m : ℕ) :
    (LevyFoundations.DensityExtension.ceilApprox t m : ℝ) =
      ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := by
  exact DensityExtension.ceilApprox_coe t m
