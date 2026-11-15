-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_constant_coefficients_zero_mean_square_error
-- name    : AppliedSDE.SarkkaSolin.euler_constant_coefficients_zero_mean_square_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:26:46.775357+00:00
-- url     : https://prove2.me/theorems/ebbe889d-0bcb-45b1-a4d6-a37764eb7583
-- title:
--   Zero mean-square Euler-Maruyama grid error for constant-coefficient SDEs
-- statement:
--   For any probability measure P, arbitrary driving paths W, constant drift b and volatility sigma, assume the exact SDE path X(t)=x0+b t+sigma(W_t-W_0), and let E satisfy the finite-grid Euler-Maruyama recurrence. Then the squared error (X(t_k)-E_k)^2 is identically zero for every grid point, and its expectation is exactly zero for every grid size. This proves the strongest possible mean-square convergence in the constant-coefficient special case and uses the exact finite-grid Euler identity already proved.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 8: Euler-Maruyama mean-square convergence.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_constant_coefficients_fin_grid
open MeasureTheory

theorem AppliedSDE.SarkkaSolin.euler_constant_coefficients_zero_mean_square_error
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ → Ω → ℝ) (n : ℕ) (T x₀ b σ : ℝ)
    (X : ℝ → Ω → ℝ) (E : Fin (n + 1) → Ω → ℝ)
    (hX : ∀ (t : ℝ) (ω : Ω),
      X t ω = x₀ + b * t + σ * (W t ω - W 0 ω))
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : Fin n) (ω : Ω),
      E k.succ ω = E k.castSucc ω + b * (T / (n : ℝ)) +
        σ * (W (((k.val + 1 : ℕ) : ℝ) * (T / (n : ℝ))) ω -
          W ((k.val : ℝ) * (T / (n : ℝ))) ω)) :
    ∀ (k : Fin (n + 1)),
      (∫ ω, (X ((k.val : ℝ) * (T / (n : ℝ))) ω - E k ω) ^ 2 ∂P) = 0 := by
  sorry
