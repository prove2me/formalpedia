-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_atTop
-- name    : AvramDividend.Classical.negative_compensated_real_integral_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:19:42.550469+00:00
-- url     : https://prove2.me/theorems/e4704c2b-8e87-4bf7-95e2-74492861e9b0
-- title:
--   Infinite negative-jump moment forces real compensated integral divergence
-- statement:
--   An arbitrary negative-jump measure with infinite extended absolute first moment has real normalised compensated exponential integrals diverging to positive infinity along integer Laplace parameters, provided each real integrand is Bochner-integrable. This bridges the genuinely infinite extended-real integral to the ordinary real integral appearing in the canonical spectrally negative Lévy exponent.
-- source:
--   Prove2Me negative_compensated_lintegral_tendsto and pinned Mathlib ofReal_integral_eq_lintegral_ofReal, Real.add_one_le_exp, and ENNReal.tendsto_ofReal_nhds_top; exact integrability is a stated hypothesis.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_real_integral_tendsto_atTop
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤)
    (hint : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν)
      atTop atTop := by sorry
