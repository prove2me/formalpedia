-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
-- name    : AvramDividend.Classical.avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:00:55.575385+00:00
-- url     : https://prove2.me/theorems/e7bc62ca-de8e-47f1-a3aa-8ac4c5ed07ab
-- title:
--   Derivative under one-sided weighted mollification from uniform domination via pinned parametric-integral calculus
-- statement:
--   Let f be a real function having derivative g at every point, where |g| is globally bounded by L. Given any measure and measurable scalar kernel weight φ with integrable absolute value and each weighted translate φ(z)f(t-εz) and φ(z)g(t-εz) integrable, the first derivative of its convolution K(t)=∫φ(z)f(t-εz) is the convolution of g. This uses pinned Mathlib's actual dominated parametric-integral differentiation theorem. It is an independent analytic bridge needed twice by Gaussian generator smoothing of the regular part of the original finite-cap value test.
-- source:
--   Source-faithful analytic derivative-interchange obligation for 0ef5d778 and Proved ec2fc3be. Unlike an assumed hDeriv, this result proves the interchange under bounded derivative and integrable kernel hypotheses.

import Mathlib
open MeasureTheory Filter Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_uniformly_dominated_weighted_smooth_shift_derivative_integral
    (μ : Measure ℝ) (φ f g : ℝ → ℝ) (ε y : ℝ)
    (hFI : ∀ t, Integrable (fun z => φ z * f (t - ε * z)) μ)
    (hGI : ∀ t, Integrable (fun z => φ z * g (t - ε * z)) μ)
    (hφI : Integrable (fun z => |φ z|) μ)
    (L : ℝ) (hL : 0 ≤ L) (hBd : ∀ t, |g t| ≤ L)
    (hd : ∀ t, HasDerivAt f (g t) t) :
    deriv (fun t => ∫ z, φ z * f (t - ε * z) ∂μ) y =
      ∫ z, φ z * g (y - ε * z) ∂μ := by sorry
