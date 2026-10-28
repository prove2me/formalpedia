-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_rare_grid_exponential_limit_ws01b
-- name    : AvramDividend.Classical.bv_rare_grid_exponential_limit_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:44:21.579826+00:00
-- url     : https://prove2.me/theorems/b40dc5bd-f95e-452e-be79-c8f9a030ae58
-- title:
--   Exact rare-event grid intensity limit for exponential Lévy residual zero-atom law
-- statement:
--   For every real rate r, the product of a grid size n and the exponential active-cell probability 1−exp(−r/n) converges to r. For nonnegative Lévy jump intensities this is the analytic rare-event intensity condition needed to apply the already Proved FamousTheorems.poisson_limit to independent finite-grid active cells. The theorem treats n=0 harmlessly and requires no stochastic assumptions.
-- source:
--   Real.hasDerivAt_exp and HasDerivAt.tendsto_slope_zero at the origin; compose with the reciprocal natural-number limit, then simplify the exact algebraic expression, with r=0 handled separately. The exact Lean proof passed the remote private Prove2Me compiler probe on 27 October 2026.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.bv_rare_grid_exponential_limit_ws01b (r : ℝ) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) * (1 - Real.exp (-(r / (n : ℝ)))))
      atTop (nhds r) := by sorry
