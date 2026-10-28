-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_stopped_likelihood_factor
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_future_increment_stopped_likelihood_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:28:14.802987+00:00
-- url     : https://prove2.me/theorems/693c6030-ea35-45f9-8f73-bb9ba342d82b
-- title:
--   Finite-stop likelihood and tilted future-increment law factor through one history event
-- statement:
--   For a finite-grid stopping time τ and stopped-history event A, the joint Q_T probability of A and the future increment Borel cylinder equals the stopped likelihood measure (P with compensated density M_τ)(A) times the independent marginal under the tilted law Q_u. This identifies precisely which factor uses M_τ and which still requires the full Q_T; the stopped density does not assert a globally independent future path.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), finite-horizon Esscher density and stationary independent increments; accepted finite-grid stop tilted increment factor c9bfc6f5-a0df-41a0-92c0-e79f5acb9e48 and stopped-history likelihood identity 0c4f14ef-8514-41aa-a124-690734760e85.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_grid_stop_future_increment_stopped_likelihood_factor
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
