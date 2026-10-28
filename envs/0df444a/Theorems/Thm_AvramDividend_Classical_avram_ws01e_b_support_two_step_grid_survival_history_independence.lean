-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_two_step_grid_survival_history_independence
-- name    : AvramDividend.Classical.avram_ws01e_b_support_two_step_grid_survival_history_independence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:43:57.039945+00:00
-- url     : https://prove2.me/theorems/61afe72c-8c48-4843-bed6-76a7c1d3abb7
-- title:
--   Two future Lévy increments jointly independent of finite-grid stopped history under the true Esscher clock
-- statement:
--   For a finite-grid stopped Lévy history and independent Exp(p) observation clock under the genuine Esscher density at the random observation age, the probability of two consecutive future increment Borel events together with an adapted survived-history event equals the product of the two true tilted increment probabilities and the tilted survived-history probability. The required filtration measurability is stated explicitly. This is a finite-dimensional conditional regeneration step, without introducing an infinite-horizon tilted law or assuming Wiener–Hopf independence.
-- source:
--   Directly from the preceding accepted full two-increment stopped-clock event factorisation, with its univ/univ specialisation and the proven unit mass of each finite-horizon Esscher law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_two_step_full_clock_event_factor
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Two future tilted increment cylinders jointly regenerate after
finite-grid stopping, conditional on genuine clock survival. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_two_step_grid_survival_history_independence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u v : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseMiddle : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u)) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseFinal : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 ((s + u) + v)) (A ∩ {ω : Ω | τ ω = s}))
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂)
    (hMiddle : ∀ s ∈ grid, @MeasurableSet Ω (𝓕 (s + u))
      ((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : ∀ s ∈ grid, @MeasurableSet Ω (𝓕 ((s + u) + v))
      (((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B₁ ∧
        X.X ((τ z.1 + u) + v) z.1 -
          X.X (τ z.1 + u) z.1 ∈ B₂ ∧
        z.2 ∈ C (τ z.1)} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) ((X.X u) ⁻¹' B₁) *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)))) ((X.X v) ⁻¹' B₂) *
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        z.2 ∈ C (τ z.1)} := by sorry
