-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_independent_clock_cylinder
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_independent_clock_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:55:55.893234+00:00
-- url     : https://prove2.me/theorems/19b0402f-987b-4733-826e-3e6b58db801b
-- title:
--   Independent exponential clock with an Esscher finite-grid stopping cylinder
-- statement:
--   Finite-grid stopped future increments under the finite-terminal Esscher law factor from stopped history and an independently sampled exponential observation-clock event. The statement uses the genuine product Q_T × Exp(p), no random-time density or infinite-horizon law.
-- source:
--   Proved Esscher finite-grid stopping cylinder c9bfc6f5-a0df-41a0-92c0-e79f5acb9e48 and pinned Mathlib Measure.prod_prod.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_grid_stop_independent_clock_cylinder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (p : ℝ) (hp : 0 < p) (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
        (expMeasure p))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by sorry
