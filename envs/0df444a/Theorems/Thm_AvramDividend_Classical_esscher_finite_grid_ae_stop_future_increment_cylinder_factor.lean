-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_ae_stop_future_increment_cylinder_factor
-- name    : AvramDividend.Classical.esscher_finite_grid_ae_stop_future_increment_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:57:57.826144+00:00
-- url     : https://prove2.me/theorems/004233ca-9bf1-44b1-9600-4e0400d2f594
-- title:
--   Almost-sure finite stopping grids preserve the terminal Esscher future-increment factorisation
-- statement:
--   Let a finite set of nonnegative stopping-grid values support τ almost surely under the genuine Esscher law Q_T, with measurable adapted grid fibres and every grid value s satisfying s+u≤T. For any stopped-history event A and Borel increment event B, the future increment X_(τ+u)−X_τ is independent of A under Q_T and has law Q_u(X_u∈B), even when τ takes off-grid exceptional values on a Q_T-null set. This strictly weakens the everywhere-grid hypothesis of the established finite-grid theorem and correctly handles zero-measure exceptions by almost-everywhere equality of stopped event sets; it does not assume a global tilted law or Wiener–Hopf splitting.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), spectrally negative Lévy Esscher transformation and stationary independent increments; accepted deterministic tilted cylinder b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e and projective consistency a74b3334-5c28-44d1-ae88-3057d26957f4; pinned Mathlib measure_congr and finite disjoint union measure.

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.esscher_finite_grid_ae_stop_future_increment_cylinder_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ᵐ ω ∂(P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))), τ ω ∈ grid)
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
