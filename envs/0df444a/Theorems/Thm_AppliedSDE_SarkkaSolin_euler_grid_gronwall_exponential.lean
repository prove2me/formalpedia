-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_grid_gronwall_exponential
-- name    : AppliedSDE.SarkkaSolin.euler_grid_gronwall_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:01:32.039837+00:00
-- url     : https://prove2.me/theorems/bbf35b3d-7b7a-465b-b023-b2d3560f0c67
-- title:
--   Uniform exponential bound for Euler–Maruyama discrete Grönwall amplification
-- statement:
--   For nonnegative c and T and positive integer n, (1+cT/n)^n is bounded by exp(cT). This standard uniform bound on the amplification factor turns the published mean-square discrete Grönwall lemma into an order-1/n terminal mean-square estimate for Euler-Maruyama, once the stochastic one-step L² estimate is proved. It supports the Open Chapter 8 theorem AppliedSDE.SarkkaSolin.euler_maruyama_strong_half_order.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations, Chapter 8, Euler-Maruyama error estimates.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_grid_gronwall_exponential
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n) :
    (1 + c * (T / n)) ^ n ≤ Real.exp (c * T) := by
  sorry
