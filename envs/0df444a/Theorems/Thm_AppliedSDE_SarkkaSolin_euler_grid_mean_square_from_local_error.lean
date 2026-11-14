-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_grid_mean_square_from_local_error
-- name    : AppliedSDE.SarkkaSolin.euler_grid_mean_square_from_local_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:04:06.593513+00:00
-- url     : https://prove2.me/theorems/0625b7d3-f271-428e-927d-4fb6e553e18b
-- title:
--   Euler–Maruyama terminal mean-square bound from a discrete local-error recurrence
-- statement:
--   Under the discrete mean-square error recurrence e(k+1)<=(1+cT/n)e(k)+c(T/n)^2, with e0<=0 and n>0, the terminal mean-square error is at most c*T*(T/n)*exp(c*T). This supplies the deterministic endgame of the Euler-Maruyama strong half-order proof after the stochastic one-step error estimate, which remains a genuine separate obligation. It combines the Proved discrete Grönwall theorem and the uniform exponential amplification lemma.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 8, strong Euler-Maruyama convergence.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_grid_mean_square_from_local_error
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (e : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hzero : e 0 ≤ 0)
    (hstep : ∀ k : ℕ,
      e (k + 1) ≤ (1 + c * (T / n)) * e k + c * (T / n) ^ 2) :
    e n ≤ c * T * (T / n) * Real.exp (c * T) := by
  sorry
