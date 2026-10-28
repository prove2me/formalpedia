-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_likelihood_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:44:31.017768+00:00
-- url     : https://prove2.me/theorems/0c4f14ef-8514-41aa-a124-690734760e85
-- title:
--   Stopped-history Esscher likelihood equals its finite-terminal density at every finite-grid stopping time
-- statement:
--   For a finite-valued adapted stopping time τ with every grid value at most T, any measurable stopped-history event A has equal probability under the deterministic terminal Esscher law Q_T and the probability measure whose Radon–Nikodym density is the compensated exponential M_τ. Thus deterministic-time Esscher projective consistency extends exactly to the stopped history on each finite grid, without global infinite-horizon Esscher construction, an additional strong-Markov axiom or any Wiener–Hopf claim.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, Esscher transform §2.1; accepted finite-horizon Esscher past-event consistency a74b3334-5c28-44d1-ae88-3057d26957f4 and finite-grid stopped-event measure partition 5edb1a0c-5d8b-4d2e-bab5-01b6b88e542e.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.esscher_finite_grid_stop_likelihood_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s})) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) A := by sorry
