-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finite_grid_stopping_increment_laplace
-- name    : AvramDividend.Classical.levy_finite_grid_stopping_increment_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:12.077225+00:00
-- url     : https://prove2.me/theorems/93aa0951-3e81-47d7-a6a9-a761465bc991
-- title:
--   Lévy increment Laplace transform after a finite-valued stopping time
-- statement:
--   For a finite grid of stopping times, assume that τ takes values only in the finite grid and the event {τ=s} is measurable in the original filtration at time s. Then the increment X_(τ+h)−X_τ has the same nonnegative-parameter Laplace transform as X_h. Decompose the expectation into finitely many indicator events {τ=s}; independence of the deterministic increment X_(s+h)−X_s from F_s permits each indicator to factor out as its probability; stationary increments and the Lévy Laplace transform make every remaining conditional exponential expectation equal exp(h ψ(θ)); the indicators partition Ω, so the probabilities sum to one. This is the finite-valued stopping-time stage of the dyadic approximation proof of bounded-stopping strong Markov, and requires no filtration usual conditions. This child is mathematically independent of the full bounded-stopping theorem.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 stopped strong-Markov step; canonical SpectrallyNegativeLevy.indepIncrements, stationaryIncrements and laplace fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finite_grid_stopping_increment_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      Real.exp ((h : ℝ) * X.ψ θ) := by sorry
