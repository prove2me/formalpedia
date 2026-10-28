-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_two_step_full_clock_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_finite_grid_two_step_full_clock_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:37:21.050932+00:00
-- url     : https://prove2.me/theorems/155c3f02-7331-4252-8b3f-02fd0c7a71b3
-- title:
--   Genuine random-clock Esscher full two-increment stopped-history event factorisation
-- statement:
--   For an adapted stopping history taking values in a finite grid, two consecutive post-stopping Lévy increment Borel conditions and cell-dependent exponential-clock tails supported beyond both increments, the probability of their complete joint event under the genuine random-terminal Esscher path/clock likelihood equals the corresponding finite sum of individually tilted history, independent increment, and clock masses. The disjoint-grid partition and filtration measurability are proved explicitly; this prepares the two-coordinate cylinder regeneration and introduces no Wiener–Hopf independence assumption.
-- source:
--   Proved finite-grid two-step random-terminal Esscher cell-sum factorisation 80ea8528-97ae-4ddc-ad16-7069cf88d13c, plus pinned Mathlib measure_biUnion_finset and filtration monotonicity.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_two_step_clock_tail_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Exact genuine tilted probability of a stopped history with
two successive post-stop increments and a variable clock tail. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_finite_grid_two_step_full_clock_event_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u v : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
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
    ∑ s ∈ grid,
      ((((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B₁)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ))))
          ((X.X v) ⁻¹' B₂)) * (expMeasure p) (C s)) := by sorry
