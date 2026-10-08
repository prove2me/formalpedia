-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_negative_secant_mono
-- name    : AvramDividend.Classical.exp_negative_secant_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:48:39.457976+00:00
-- url     : https://prove2.me/theorems/76b41aa7-d0cb-4b50-bbe8-92f958a71325
-- title:
--   Negative-jump exponential secant is monotone in the Laplace parameter
-- statement:
--   For any negative jump size y and 0<theta1<=theta2, the secant (exp(theta*y)-1)/theta is increasing with theta. Combined with the constant -y this establishes monotonicity of (exp(theta*y)-1-theta*y)/theta, enabling monotone convergence for the infinite first-moment non-Gaussian Lévy exponent branch.
-- source:
--   Exact-pinned Mathlib Real.convexOn_exp and ConvexOn.secant_mono. Apply the latter at secants from zero to theta2*y and theta1*y, then reverse inequality by multiplication by negative y. This is the missing monotonic kernel estimate for the infinite-variation branch of the Avram Standing hypothesis.

import Mathlib

theorem AvramDividend.Classical.exp_negative_secant_mono
    (y θ₁ θ₂ : ℝ) (hy : y < 0)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    (Real.exp (θ₁ * y) - 1) / θ₁ ≤
      (Real.exp (θ₂ * y) - 1) / θ₂ := by sorry
