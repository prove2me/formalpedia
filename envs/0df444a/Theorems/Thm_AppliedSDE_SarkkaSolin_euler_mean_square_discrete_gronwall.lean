-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_mean_square_discrete_gronwall
-- name    : AppliedSDE.SarkkaSolin.euler_mean_square_discrete_gronwall
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:41:37.982326+00:00
-- url     : https://prove2.me/theorems/3036f156-3cfb-4228-945f-ae18a9ce03ab
-- title:
--   Discrete Grönwall bound for Euler–Maruyama mean-square errors
-- statement:
--   For nonnegative constants c and h, any error sequence satisfying e_0<=0 and e_{n+1}<=(1+c h)e_n+c h^2 obeys e_n<=c h^2 n (1+c h)^n. This deterministic inequality is the error-propagation component needed to obtain the strong order one-half of Euler-Maruyama, the Open Chapter 8 Applied SDE theorem 3261cdf6-e9b9-4d64-9632-5fbb342fd2c2. The separate stochastic local-error estimate is not assumed to follow from this result.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, numerical SDE methods, Euler-Maruyama strong convergence.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_mean_square_discrete_gronwall
    (h c : ℝ) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (e : ℕ → ℝ)
    (hzero : e 0 ≤ 0)
    (hstep : ∀ n : ℕ,
      e (n + 1) ≤ (1 + c * h) * e n + c * h ^ 2) :
    ∀ n : ℕ,
      e n ≤ c * h ^ 2 * (n : ℝ) * (1 + c * h) ^ n := by
  sorry
