-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_lipschitz_squared_sum
-- name    : AppliedSDE.SarkkaSolin.euler_lipschitz_squared_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:55:34.539746+00:00
-- url     : https://prove2.me/theorems/70bc9aa3-ccb9-4933-8400-9203135b60b3
-- title:
--   Joint squared Lipschitz drift and diffusion estimate for Euler-Maruyama
-- statement:
--   If the drift b and volatility sigma are both globally Lipschitz with constant L >= 0, their combined squared increments are bounded by 2L² times squared state displacement. This inequality is the deterministic coefficient-estimate input to Euler-Maruyama mean-square local error recurrence.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 8, strong convergence of Euler-Maruyama.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_lipschitz_squared_sum
    (b σ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (x y : ℝ) :
    |b x - b y| ^ 2 + |σ x - σ y| ^ 2 ≤
      2 * L ^ 2 * |x - y| ^ 2 := by
  sorry
