-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_fpk_gaussian_constant_drift
-- name    : AppliedSDE.SarkkaSolin.fpk_gaussian_constant_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:46:27.089601+00:00
-- url     : https://prove2.me/theorems/42c16e46-7d9b-4591-a070-70f18572bb2e
-- title:
--   One-dimensional Gaussian transition density solves the forward Kolmogorov equation
-- statement:
--   Theorem 5.4 and eq (5.11), printed pp. 61–62. This draft proves a nonzero constant-drift, constant-variance specialisation of the forward Fokker–Planck–Kolmogorov equation. The density is the Gaussian fundamental solution of the SDE dX=b dt+sqrt(q) dW. The general state-dependent coefficient theorem remains a separate source obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \partial_t p(t,x)=-b\,\partial_xp(t,x)+\frac q2\,\partial_x^2p(t,x)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.4, equation (5.11), constant-drift scalar specialisation, printed p. 61. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.fpk_gaussian_constant_drift
    (b q y s x t : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ → ℝ → ℝ := fun z τ =>
      Real.exp (-((z - y - b * (τ - s)) ^ 2 / (2 * q * (τ - s)))) /
        Real.sqrt (2 * Real.pi * q * (τ - s));
    deriv (fun τ => p x τ) t =
      -b * deriv (fun z => p z t) x +
        q / 2 * deriv (fun z => deriv (fun w => p w t) z) x := by
  sorry
