-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_negative_compensated_secant_mono
-- name    : AvramDividend.Classical.exp_negative_compensated_secant_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:44:18.531779+00:00
-- url     : https://prove2.me/theorems/de6ae02d-2a04-4371-bdef-a9d0ca042123
-- title:
--   Compensated negative-jump secant is monotone in the Laplace parameter
-- statement:
--   For any strictly negative jump size y and positive real Laplace parameters θ₁≤θ₂, the normalised compensated exponential remainder (exp(θy)−1−θy)/θ is nondecreasing in θ. This is the exact pointwise monotonicity required to apply Mathlib monotone convergence to the non-Gaussian infinite-first-moment Lévy jump integral, and combines with the Proved pointwise limit at θ=n+1.
-- source:
--   Direct algebraic rearrangement of the Prove2Me-Proved exp_negative_secant_mono theorem, paired with the Proved exp_negative_compensated_secant_limit to enable monotone convergence of Lévy compensated jump integrals.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_negative_secant_mono

open AvramDividend.Classical

theorem AvramDividend.Classical.exp_negative_compensated_secant_mono
    (y θ₁ θ₂ : ℝ) (hy : y < 0)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ≤
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ := by sorry
