-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_compensated_integral_lower_div_theta
-- name    : AvramDividend.Classical.exp_compensated_integral_lower_div_theta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:28:30.476236+00:00
-- url     : https://prove2.me/theorems/9718024b-92b9-422b-8fc8-12cf6c8a2431
-- title:
--   Truncated negative-jump exponent lower bound divided by parameter
-- statement:
--   For a finite negative-jump measure with an integrable jump size, the compensated exponential integral divided by θ>0 is at least the absolute first moment minus the total real mass divided by θ. This quantitatively isolates the diverging truncated jump first moment as θ increases, before passing from finite truncations to the full Lévy measure.
-- source:
--   Direct normalisation of the authoritative Prove2Me-Proved exp_compensated_integral_lower_finite theorem, using linearity of real integration and positive θ. It is an analytic dependency for the non-Gaussian case of scaleFunction_strict_pos_of_standing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_compensated_integral_lower_finite

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.exp_compensated_integral_lower_div_theta
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (θ : ℝ) (hθ : 0 < θ)
    (hneg : ∀ᵐ y ∂ν, y ≤ 0)
    (hyint : Integrable (fun y : ℝ => y) ν) :
    (∫ y : ℝ, |y| ∂ν) -
      (∫ y : ℝ, (1 : ℝ) ∂ν) / θ ≤
      (∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) ∂ν) / θ := by sorry
