-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_constant_drift_brownian_likelihood_ratio
-- name    : AppliedSDE.SarkkaSolin.constant_drift_brownian_likelihood_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:47:17.90279+00:00
-- url     : https://prove2.me/theorems/dd3e7577-502c-4d6c-9509-5907ad288264
-- title:
--   Gaussian likelihood ratio against standard Brownian motion
-- statement:
--   Corollary 7.6, equation (7.42), printed p. 107. For a constant drift b and variance q, the endpoint density relative to driftless Brownian motion equals exp(b x/q − b² t/(2q)). The path-functional extension remains an independent target.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \frac{p_b(x,t\mid0)}{p_0(x,t\mid0)}=\exp\!\left(\frac{bx}q-\frac{b^2t}{2q}\right)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Corollary 7.6, equation (7.42), constant-drift endpoint case, printed p. 107. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.constant_drift_brownian_likelihood_ratio
    (b q t x : ℝ) (hq : 0 < q) (ht : 0 < t) :
    let gaussian : ℝ → ℝ := fun u =>
      Real.exp (-((x - u * t) ^ 2 / (2 * q * t))) /
        Real.sqrt (2 * Real.pi * q * t)
    gaussian b = Real.exp (b * x / q - b ^ 2 * t / (2 * q)) *
      gaussian 0 := by
  sorry
