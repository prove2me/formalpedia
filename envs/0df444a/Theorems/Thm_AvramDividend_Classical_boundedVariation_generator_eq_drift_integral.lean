-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral
-- name    : AvramDividend.Classical.boundedVariation_generator_eq_drift_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:44:06.454392+00:00
-- url     : https://prove2.me/theorems/40032839-88a5-4433-b56b-d2c794dfa691
-- title:
--   The bounded-variation Lévy generator has no Gaussian second-derivative term
-- statement:
--   When a spectrally negative Lévy process has bounded variation, its Gaussian coefficient vanishes. Its generator acting on any test function therefore consists exactly of the linear drift term and the compensated jump integral, without a second derivative requirement. This is the generator normalisation needed before applying the C1 finite-variation verification argument.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_generator_eq_drift_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    X.generator w x =
      X.c * deriv w x +
        ∫ y in Iio (0 : ℝ), (w (x + y) - w x - deriv w x * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν := by sorry
