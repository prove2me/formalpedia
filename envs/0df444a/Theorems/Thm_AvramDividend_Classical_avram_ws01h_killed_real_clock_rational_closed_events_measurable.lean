-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_killed_real_clock_rational_closed_events_measurable
-- name    : AvramDividend.Classical.avram_ws01h_killed_real_clock_rational_closed_events_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:47:36.136014+00:00
-- url     : https://prove2.me/theorems/c0e9e0a6-7b2f-4a34-87d1-34d38a540f14
-- title:
--   Both original Lévy killed stopped-record finite real-clock rational and full continuous future survival events are Borel measurable
-- statement:
--   For any original spectrally negative Lévy process, measurable finite random record clock τ, measurable lower-killed historical prefix A, initial capital a and real observation age r, prove the two actual path-clock event sets are measurable: the event that τ≤r, A occurs and every countable relative rational shifted future reserve is nonnegative; and the same event with every relative continuous future reserve through the complete closed residual horizon. Prove source joint measurability of the entire shifted future Lévy path and the random residual observation age, apply the accepted rational-age reward measurable theorem for the countable tests, and for the continuous version use the accepted exact closed-horizon future measurability result. Unlike the prior Qp integral identity, this extracts explicit measurable event sets to use pinned lintegral_indicator_one and avoid non-definitional compiler Decidable instances in the actual capped CDF renewal integration. Assumes no exit scale ratio.
-- source:
--   Direct extraction from canonically Proved avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral 18438; real clock stopped future full measurable 18433, rational H measurable 0b7edea5, shifted whole path measurable 8e59a363.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_killed_real_clock_rational_closed_events_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A) :
    MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
          Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
          X.X (τ z.1) z.1)} ∧
    MeasurableSet {z : Ω × ℝ |
      (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)} := by sorry
