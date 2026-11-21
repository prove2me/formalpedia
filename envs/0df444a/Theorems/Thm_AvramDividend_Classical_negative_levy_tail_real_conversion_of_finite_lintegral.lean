-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_tail_real_conversion_of_finite_lintegral
-- name    : AvramDividend.Classical.negative_levy_tail_real_conversion_of_finite_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:50:29.108395+00:00
-- url     : https://prove2.me/theorems/d7387618-810b-417b-9c26-4a66a131ec27
-- title:
--   Convert finite ENNReal original negative Lévy-tail transform to integrable real tail
-- statement:
--   For any measure ν whose negative tails ν((-∞,-t)) are finite at every t>0 and any θ>0, a finite ENNReal integral of the nonnegative compensated weight (1-exp(-θt)) against this tail implies integrability of the corresponding real-valued tail kernel and equality of its real integral to the ENNReal total converted toReal. This is the genuinely measurable/finite real conversion needed for the original Lévy exponent-to-tail identity; the theorem assumes no stochastic process or Lévy quadratic condition.
-- source:
--   Pinned Mathlib monotone-measurable, lintegral_ofReal_ne_top_iff_integrable, ofReal_integral_eq_lintegral_ofReal, integral_nonneg_of_ae; Proved pointwise kernel bound 1eaa6bca; original bridge 59a18d19.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_levy_tail_real_conversion_of_finite_lintegral
    (ν : Measure ℝ)
    (hTailFin : ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (L : ℝ≥0∞) (hLfinite : L ≠ ⊤)
    (hTon : (∫⁻ t in Ioi (0 : ℝ),
        ν (Iio (-t)) * ENNReal.ofReal (1 - Real.exp (-θ * t))) = L) :
    IntegrableOn (fun t : ℝ =>
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) =
      L.toReal := by sorry
