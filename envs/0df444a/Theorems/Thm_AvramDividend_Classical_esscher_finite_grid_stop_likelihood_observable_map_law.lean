-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_observable_map_law
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_likelihood_observable_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:40:35.906711+00:00
-- url     : https://prove2.me/theorems/c9fbbdc2-3b2e-4d4b-899a-c810d5e2ed2f
-- title:
--   All measurable-space-valued stopped-history observables have the same finite-grid Esscher law under terminal and stopped densities
-- statement:
--   Let τ be an adapted finite-grid stopping time no later than terminal T, and Z a random observable taking values in any measurable space α. If each Borel preimage of Z restricted to the fibre {τ=s} belongs to F_s, then Z is automatically globally measurable and its full pushed-forward law under the deterministic terminal Esscher probability Q_T equals its pushed-forward law under the stopped exponential density P.withDensity M_τ. This strengthens event-level stopped-history change of measure to arbitrary stopped-history observables, without a global Q∞ or WH splitting.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), finite-horizon Esscher density; accepted stopped-history likelihood theorem 0c4f14ef-8514-41aa-a124-690734760e85; pinned Mathlib Finset.measurableSet_biUnion, Measure.map_apply and Measure.ext.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.esscher_finite_grid_stop_likelihood_observable_map_law
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (Z : Ω → α)
    (hZhistory : ∀ s ∈ grid, ∀ B : Set α, MeasurableSet B →
      MeasurableSet[𝓕 s] (Z ⁻¹' B ∩ {ω : Ω | τ ω = s})) :
    Measure.map Z
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map Z
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by sorry
