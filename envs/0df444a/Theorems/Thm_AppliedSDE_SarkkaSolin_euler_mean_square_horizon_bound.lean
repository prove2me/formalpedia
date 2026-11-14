-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_mean_square_horizon_bound
-- name    : AppliedSDE.SarkkaSolin.euler_mean_square_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:31:08.127965+00:00
-- url     : https://prove2.me/theorems/b1a31fd4-3dea-46ad-be9a-e6a8cb2af556
-- title:
--   Finite-horizon O(h) mean-square Euler error bound by discrete Grönwall
-- statement:
--   Assume a nonnegative step size h, nonnegative constant c and a discrete error recurrence e_{n+1}<=(1+ch)e_n+ch² with e_0<=0. For every grid index with n h<=T, the mean-square error is bounded by c h T exp(cT). This is the deterministic final step in Euler-Maruyama strong half-order convergence and explicitly imports the previously Proved discrete Gronwall lemma. Establishing the stochastic one-step error inequality remains an independent obligation.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 8 Euler-Maruyama strong convergence.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_mean_square_discrete_gronwall

theorem AppliedSDE.SarkkaSolin.euler_mean_square_horizon_bound
    (h c T : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (e : ℕ → ℝ) (hzero : e 0 ≤ 0)
    (hstep : ∀ n : ℕ,
      e (n + 1) ≤ (1 + c * h) * e n + c * h ^ 2) :
    ∀ n : ℕ, (n : ℝ) * h ≤ T →
      e n ≤ c * h * T * Real.exp (c * T) := by
  sorry
