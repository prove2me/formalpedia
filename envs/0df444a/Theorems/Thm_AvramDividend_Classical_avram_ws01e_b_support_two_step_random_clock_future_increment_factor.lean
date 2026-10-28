-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_two_step_random_clock_future_increment_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_two_step_random_clock_future_increment_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:24:11.254966+00:00
-- url     : https://prove2.me/theorems/0b709ce6-8839-4979-88d5-a2ecd04fe0f6
-- title:
--   Two successive future Esscher increments factor at a genuine exponential observation clock
-- statement:
--   Let A be measurable at time s, let B₁ and B₂ be Borel future-increment events over successive lengths u and v, and let C be an exponential observation-clock set entirely after s+u+v. Under the actual joint random-observation Esscher density, the joint probability of A, both future increments, and C factors exactly into the Esscher history probability at s, individual u and v Esscher increment probabilities, and the independent exponential-clock mass. The two-step cylinder conditions are explicitly assumed adapted. This is a valid finite-dimensional precursor to the full post-record path factorisation needed for Wiener-Hopf independence.
-- source:
--   Composes the canonically Proved esscher_random_time_joint_past_clock_future_factorization (caa0f80f-72fe-4f00-ad06-c2fe43ac38d4) with two successive applications of esscher_terminal_increment_cylinder_factorization (b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e).

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Two consecutive future-increment cylinders factor under the actual
random-clock Esscher law on a clock tail beyond both increments. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_two_step_random_clock_future_increment_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (s u v : ℝ≥0)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂)
    (hMiddle : @MeasurableSet Ω (𝓕 (s + u))
      (A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : @MeasurableSet Ω (𝓕 ((s + u) + v))
      ((A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂))
    (C : Set ℝ) (hC : MeasurableSet C)
    (hClockTail : ∀ t ∈ C, (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      (((A ∩ (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
        (fun ω : Ω => X.X ((s + u) + v) ω -
          X.X (s + u) ω) ⁻¹' B₂) ×ˢ C) =
    (((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B₁)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ))))
          ((X.X v) ⁻¹' B₂)) * (expMeasure p) C := by sorry
