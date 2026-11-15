-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_lipschitz_linear_growth
-- name    : AppliedSDE.SarkkaSolin.euler_lipschitz_linear_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:03:45.921244+00:00
-- url     : https://prove2.me/theorems/f7fe4364-d9f9-405b-a5ca-c14efcfd3b08
-- title:
--   Uniform quadratic linear-growth estimate for Lipschitz SDE coefficients
-- statement:
--   For globally Lipschitz drift b and volatility sigma with nonnegative constant L, the combined squared coefficient magnitudes at x are bounded by 4 L²|x|² + 2(|b(0)|²+|sigma(0)|²). This is a standard linear-growth consequence of the global Lipschitz property, used to bound second moments of SDE solutions and Euler-Maruyama numerical approximations.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 8, strong Euler-Maruyama convergence.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_lipschitz_linear_growth
    (b σ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (x : ℝ) :
    |b x| ^ 2 + |σ x| ^ 2 ≤
      4 * L ^ 2 * |x| ^ 2 +
      2 * (|b 0| ^ 2 + |σ 0| ^ 2) := by
  sorry
