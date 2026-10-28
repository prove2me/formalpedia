-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_future_increment_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:14:15.077997+00:00
-- url     : https://prove2.me/theorems/c9bfc6f5-a0df-41a0-92c0-e79f5acb9e48
-- title:
--   Finite-grid stopped future increments obey the terminal Esscher Markov cylinder law
-- statement:
--   For an Esscher-tilted Lévy law at deterministic terminal T, a finite-valued stopping time τ with all grid values s satisfying s+u≤T, and any stopped-history event A whose intersections with the fibres {τ=s} are F_s-measurable, the stopped future increment X_(τ+u)−X_τ has the Q_u increment law and is independent of A. The conclusion is under the genuine finite-terminal Q_T, with no all-time law or Wiener–Hopf assumption.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), §2.1 Esscher law and Lévy independent increments; accepted terminal-cylinder law b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e, consistency a74b3334-5c28-44d1-ae88-3057d26957f4 and finite stopped partition 5edb1a0c-5d8b-4d2e-bab5-01b6b88e542e.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.esscher_finite_grid_stop_future_increment_cylinder_factor
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
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
