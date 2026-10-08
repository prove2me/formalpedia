-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
-- name    : AvramDividend.Classical.levy_compensated_jump_integrable_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:34:35.721371+00:00
-- url     : https://prove2.me/theorems/1f95f376-3248-4dd4-9c0b-855c9ce11488
-- title:
--   Canonical Lévy jump integrability at every nonnegative parameter
-- statement:
--   For the spectrally negative Lévy process in the Avram framework, the compensated negative-jump integrand is integrable against its Lévy measure for every nonnegative Laplace parameter. This discharges the explicit remaining jump-integrability premise in the proved Gaussian eventual-exponent theorem.
-- source:
--   The Lévy-measure condition ν_integrable; exp_neg_remainder_bounds; and the accepted integrability argument in psi_quadratic_upper. Bound the compensated integrand by (1+θ²)min(1,y²), using small-jump second moments and finite large-jump mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_jump_integrable_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ =>
      Real.exp (θ * y) - 1 -
        θ * y * ((Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) X.ν := by sorry
