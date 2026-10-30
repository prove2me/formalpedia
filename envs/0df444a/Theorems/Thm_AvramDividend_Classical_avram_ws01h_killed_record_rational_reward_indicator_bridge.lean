-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_record_rational_reward_indicator_bridge
-- name    : AvramDividend.Classical.avram_ws01h_killed_record_rational_reward_indicator_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:23:26.313028+00:00
-- url     : https://prove2.me/theorems/92d06a1e-aad9-431b-94a8-b783a0ba25e7
-- title:
--   Exact lower-killed stopped record weight times rational future reward integrates as the genuine rational record event indicator
-- statement:
--   For every genuine or arbitrary measure μ on original sample paths and a real observation clock, any measurable stopped age τ and killed-history event A, the source-shaped stopped prefix indicator (if τ≤r then 1_A·1_{all relative rational future reserve tests} else 0) is pointwise exactly the indicator of the corresponding true record-followed-by-rational-survival event. Thus their lintegrals under the actual terminal Esscher joint Qp, or any measure, are equal without stochastic assumptions or scale formula. This explicit source event bridge makes the canonically proved lower-killed true Qp stopped full-future Markov factor usable with the independent accepted rational-to-continuous Qp event mass identity.
-- source:
--   Pinned Mathlib Set.indicator and lintegral_congr; direct source stopped/history/event definition. No canonical two-sided exit imported.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_killed_record_rational_reward_indicator_bridge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (Ω × ℝ)) (τ : Ω → ℝ≥0) (A : Set Ω)
    (Y : Ω → (ℝ≥0 → ℝ)) (a : ℝ) :
    (let B : Set (Ω × ℝ) := {z | (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
           0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)}
     let H : Ω × ℝ → ℝ≥0∞ := fun z =>
       if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
           0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
       then 1 else 0
     (∫⁻ z, if (τ z.1 : ℝ) ≤ z.2 then
        (if z.1 ∈ A then (1 : ℝ≥0∞) else 0) * H z else 0 ∂μ) =
     (∫⁻ z, B.indicator (fun _ => (1 : ℝ≥0∞)) z ∂μ)) := by sorry
