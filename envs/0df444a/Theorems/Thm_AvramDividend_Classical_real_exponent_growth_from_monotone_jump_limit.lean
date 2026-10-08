-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_exponent_growth_from_monotone_jump_limit
-- name    : AvramDividend.Classical.real_exponent_growth_from_monotone_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:24:24.251607+00:00
-- url     : https://prove2.me/theorems/8d164d45-77db-4875-b1a4-9709041ecc30
-- title:
--   Monotone jump limit and canonical exponent comparison imply eventual growth on all real parameters
-- statement:
--   Suppose the normalised small-negative-jump integral f(θ) is nondecreasing for positive real θ and c+f(n+1) converges along integers to d>0. If a Lévy exponent ψ satisfies ψ(θ)/θ≥c+f(θ)−B/θ for some finite B≥0, then ψ(θ)>q for every sufficiently large real θ, for any q. This is the precise bridge needed in the bounded-variation positive-drift case without an unjustified extrapolation from integer Laplace parameters.
-- source:
--   Mathlib order-filter convergence, positivity, real-parameter monotonicity and explicit large-θ bounds, abstracting the Prove2Me-Proved canonical psi lower bound, compensated-integral monotonicity, DCT and drift positivity.

import Mathlib

open Filter

theorem AvramDividend.Classical.real_exponent_growth_from_monotone_jump_limit
    (ψ f : ℝ → ℝ) (c B d q : ℝ) (hB : 0 ≤ B) (hd : 0 < d)
    (hfmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → f θ₁ ≤ f θ₂)
    (hseq : Filter.Tendsto (fun n : ℕ => c + f ((n : ℝ) + 1))
      Filter.atTop (nhds d))
    (hlower : ∀ θ : ℝ, 0 < θ →
      c + f θ - B / θ ≤ ψ θ / θ) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → q < ψ θ := by sorry
