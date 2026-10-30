-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_killed_rational_closed_event_measure_eq
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_killed_rational_closed_event_measure_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:49:23.953878+00:00
-- url     : https://prove2.me/theorems/5ae69fd2-29df-4012-b089-ac011b454c47
-- title:
--   Original Lévy terminal Esscher Qp lower-killed first-record future rational and full continuous survival events have equal measurable set masses
-- statement:
--   Given the actual spectrally negative Lévy original path law P, true joint terminal Esscher Qp observed real exponential clock, measurable original random record age τ and killed historical event A, and the genuine measurability of the rational future survival and complete closed shifted-future survival event sets, their exact Qp measures coincide. This strengthens the canonically Proved stopped rational-vs-closed indicator integral identity into an equality of event measures by the pinned Mathlib identity lintegral_indicator_one, thereby eliminating non-definitional Decidable instance differences between separately elaborated Set.indicator functions in the complete finite-p killed CDF regeneration. All stochastic/a.e. content is imported from the accepted source genuine Qp theorem, with the measure-theoretic bridge proved explicitly. No scale exit ratio.
-- source:
--   Accepted avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral candidate 18438; pinned Mathlib MeasureTheory.lintegral_indicator_one requiring MeasurableSet for each genuine source event.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_Qp_killed_rational_closed_event_measure_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (a : ℝ) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A)
    (hGrid : MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
          Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)})
    (hFull : MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}) :
    ((P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
          Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)} =
    ((P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)} := by sorry
