-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_euler_constant_coefficients_fin_grid
-- name    : AppliedSDE.SarkkaSolin.euler_constant_coefficients_fin_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:22:47.176982+00:00
-- url     : https://prove2.me/theorems/46616816-17ea-42e8-9bc5-511f8e2162e9
-- title:
--   Exact constant-coefficient Euler-Maruyama solution with Fin(n+1) grid indexing
-- statement:
--   For arbitrary real-valued driving paths W and constant drift and diffusion coefficients, any Euler-Maruyama finite-grid recursion with grid indices Fin(n+1) and step T/n has the exact closed-form solution E_k=x0+b(kT/n)+sigma(W_(kT/n)-W_0). The statement uses the same Fin-indexed initial-state and successor recurrence structure as the Särkkä-Solin Chapter 8 strong-convergence milestone, providing a directly reusable exactness lemma for the constant-coefficient case.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 8: Euler-Maruyama scheme.

import Mathlib

theorem AppliedSDE.SarkkaSolin.euler_constant_coefficients_fin_grid
    {Ω : Type*} (W : ℝ → Ω → ℝ)
    (n : ℕ) (T x₀ b σ : ℝ)
    (E : Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : Fin n) (ω : Ω),
      E k.succ ω = E k.castSucc ω + b * (T / (n : ℝ)) +
        σ * (W (((k.val + 1 : ℕ) : ℝ) * (T / (n : ℝ))) ω -
          W ((k.val : ℝ) * (T / (n : ℝ))) ω)) :
    ∀ (k : Fin (n + 1)) (ω : Ω),
      E k ω = x₀ + b * ((k.val : ℝ) * (T / (n : ℝ))) +
        σ * (W ((k.val : ℝ) * (T / (n : ℝ))) ω - W 0 ω) := by
  sorry
