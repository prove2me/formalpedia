-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_constant_drift_gaussian_likelihood_ratio
-- name    : AppliedSDE.SarkkaSolin.constant_drift_gaussian_likelihood_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:47:05.48084+00:00
-- url     : https://prove2.me/theorems/591c0a50-0408-4462-9111-1c5eb636d2d1
-- title:
--   Gaussian likelihood ratio between two constant-drift diffusions
-- statement:
--   Theorem 7.4, equations (7.36)–(7.38), printed pp. 105–106. For positive time and variance q, with initial state zero, the endpoint Gaussian density under drift b is the drift-c density multiplied by the exact exponential likelihood ratio. This is a finite-time scalar specialisation of the book's path-law Radon–Nikodym theorem.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \frac{p_b(x,t\mid0)}{p_c(x,t\mid0)}=\exp\!\left(\frac{(b-c)x}q-\frac{(b^2-c^2)t}{2q}\right)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.4, equations (7.36)–(7.38), constant-drift endpoint case, printed pp. 105–106. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.constant_drift_gaussian_likelihood_ratio
    (b c q t x : ℝ) (hq : 0 < q) (ht : 0 < t) :
    let p : ℝ → ℝ := fun u =>
      Real.exp (-((x - u * t) ^ 2 / (2 * q * t))) /
        Real.sqrt (2 * Real.pi * q * t)
    p b = Real.exp ((b - c) * x / q -
      (b ^ 2 - c ^ 2) * t / (2 * q)) * p c := by
  sorry
