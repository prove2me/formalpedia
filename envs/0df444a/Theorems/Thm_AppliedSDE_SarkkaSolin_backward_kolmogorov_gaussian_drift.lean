-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_backward_kolmogorov_gaussian_drift
-- name    : AppliedSDE.SarkkaSolin.backward_kolmogorov_gaussian_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:46:52.578686+00:00
-- url     : https://prove2.me/theorems/0fda7328-b552-40b9-83b5-e9d2e94d9332
-- title:
--   Nonzero-drift Gaussian transition density solves the backward Kolmogorov equation
-- statement:
--   Theorem 5.11 and eq (5.44), printed p. 68. For a constant-drift, constant-diffusion scalar SDE, differentiate the Gaussian transition density with respect to the starting time and state. The negative starting-time derivative equals the generator applied in the starting-state variable. The source printed equation has a negative starting-time derivative, and the general state-dependent theorem remains a separate obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   -\partial_s p(s,y;t,x)=b\,\partial_yp(s,y;t,x)+\frac q2\,\partial_y^2p(s,y;t,x)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.11, equation (5.44), constant-drift Gaussian case, printed p. 68. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology

theorem AppliedSDE.SarkkaSolin.backward_kolmogorov_gaussian_drift
    (b q x t y s : ℝ) (hq : 0 < q) (hst : s < t) :
    let p : ℝ → ℝ → ℝ := fun z τ =>
      Real.exp (-((x - z - b * (t - τ)) ^ 2 / (2 * q * (t - τ)))) /
        Real.sqrt (2 * Real.pi * q * (t - τ));
    -(deriv (fun τ => p y τ) s) =
      b * deriv (fun z => p z s) y +
        q / 2 * deriv (fun z => deriv (fun w => p w s) z) y := by
  sorry
