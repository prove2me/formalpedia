-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_two_step_clock_tail_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_finite_grid_two_step_clock_tail_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:27:56.923984+00:00
-- url     : https://prove2.me/theorems/80ea8528-97ae-4ddc-ad16-7069cf88d13c
-- title:
--   Finite-grid stopping histories and two future Esscher increments under cell-dependent exponential-clock tails
-- statement:
--   For each stopping-time grid cell, the true random-terminal Esscher probability of an adapted history event and two successive future-increment Borel cylinders over lengths u and v, observed on an independent exponential-clock set above s+u+v, factors into the s-time tilted history mass, individual tilted increment probabilities, and the clock mass. Summing over cells proves finite-dimensional independence on a variable random-clock support, a stepping stone to the future-path cylinder π-system.
-- source:
--   Direct finite-sum composition of accepted Esscher random-time past/clock factorisation caa0f80f-72fe-4f00-ad06-c2fe43ac38d4 and accepted fixed-terminal increment factor b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e, twice per grid cell.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Grid-dependent random-clock tails factor two successive
future increments from the adapted stopping-cell history. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_finite_grid_two_step_clock_tail_factor
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
    (∑ s ∈ grid,
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      ((((A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂) ×ˢ C s)) =
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
