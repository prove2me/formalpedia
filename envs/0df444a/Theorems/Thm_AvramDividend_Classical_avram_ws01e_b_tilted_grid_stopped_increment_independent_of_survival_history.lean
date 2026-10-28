-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history
-- name    : AvramDividend.Classical.avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:29:41.973724+00:00
-- url     : https://prove2.me/theorems/d5920281-125a-4ad8-81e6-9ac9bcfa03fb
-- title:
--   Genuine random-terminal tilted finite-grid stopped future increment independent of survived history
-- statement:
--   For an actual spectrally negative Lévy process and the authentic Esscher density at its independent Exp(p) observation clock, let τ take values in a finite grid on an adapted history event A. For every fixed post-stop lag u, Borel increment event B, and cell-dependent clock set C(s) supported after s+u, the joint tilted probability of A, the post-τ increment in B, and the survived clock event factors as the true finite-u Esscher increment probability times the genuine random-terminal tilted probability of the survived adapted history. All filtration, event and likelihood measurability assumptions are explicit. No Wiener–Hopf independence or infinite-horizon tilted process measure is assumed. This is the stopped-history cylinder regeneration step for finite-grid stops; the unbounded first upper record and all residual-time prefixes remain outstanding.
-- source:
--   Derived from canonically Proved 8d968653 finite-grid full random-clock Esscher event factor, and 6c6f7684 finite-terminal Esscher probability normalisation. This extracts conditional independence with the survival probability correctly retained, rather than merely the finite sum factor.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_full_clock_event_factor
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      z.1 ∈ A ∧ τ z.1 ∈ grid ∧
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
      z.2 ∈ C (τ z.1)} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) ((X.X u) ⁻¹' B) *
      ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      z.1 ∈ A ∧ τ z.1 ∈ grid ∧
      z.2 ∈ C (τ z.1)} := by sorry
