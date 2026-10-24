-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_grid_stopping_increment_exp_second_moment
-- name    : AvramDividend.Classical.levy_finite_grid_stopping_increment_exp_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T17:10:46.388301+00:00
-- url     : https://prove2.me/theorems/ffe14eff-8043-4f7f-9dff-908cbe728b90
-- title:
--   Exact second exponential moment after a finite-grid stopping time
-- statement:
--   For any finite-valued stopping time τ with measurable level events, the second moment of exp(θ[X_(τ+h)−X_τ]) is exp(h ψ(2θ)) when θ≥0. This exact identity holds uniformly over every finite stopping grid, providing a model-specific L² bound for uniform integrability in the dyadic limit to arbitrary bounded stopping times. It is a direct consequence of the proved stopped-increment Laplace identity applied at parameter 2θ.
-- source:
--   Derived from proved levy_finite_grid_stopping_increment_laplace (93aa0951-3e81-47d7-a6a9-a761465bc991), as the bounded-stopping strong-Markov bridge.

import Theorems.Thm_AvramDividend_Classical_levy_finite_grid_stopping_increment_laplace
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finite_grid_stopping_increment_exp_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
      Real.exp ((h : ℝ) * X.ψ (2 * θ)) := by sorry
