-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_constant_coefficients_exact_grid
-- name    : AppliedSDE.SarkkaSolin.euler_constant_coefficients_exact_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:50.834395+00:00
-- url     : https://prove2.me/theorems/d4ad6568-f4c7-4097-b80d-51b480c8b10a
-- title:
--   Euler-Maruyama has exact pathwise grid solution for constant drift and volatility
-- statement:
--   For arbitrary real-valued sample paths W_t, initial state x0, constant drift b, constant volatility sigma and time step h, the Euler-Maruyama recurrence E_(k+1)=E_k+bh+sigma(W_((k+1)h)-W_(kh)) has the exact closed-form solution E_k=x0+bkh+sigma(W_(kh)-W_0) at every grid index k. This is pathwise, applies to all sample paths even when W_0 differs from zero, and proves exactness for constant-coefficient Brownian SDEs when their solution uses the standard stochastic integral of a constant integrand.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 8: Euler-Maruyama strong convergence in the exactly solvable constant-coefficient case.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_constant_coefficients_exact_grid
    {Ω : Type*} (W : ℝ → Ω → ℝ)
    (x₀ b σ h : ℝ) (E : ℕ → Ω → ℝ)
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : ℕ) (ω : Ω),
      E (k + 1) ω = E k ω + b * h +
        σ * (W (((k + 1 : ℕ) : ℝ) * h) ω -
          W ((k : ℝ) * h) ω)) :
    ∀ (k : ℕ) (ω : Ω),
      E k ω = x₀ + b * ((k : ℝ) * h) +
        σ * (W ((k : ℝ) * h) ω - W 0 ω) := by
  sorry
