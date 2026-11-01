-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_nnreal_countable_summable
-- name    : AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_nnreal_countable_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:18:14.903114+00:00
-- url     : https://prove2.me/theorems/ac2862d2-cd83-4f11-b34a-91801f7dfd65
-- title:
--   Complete NNReal-indexed right-dividend jump support is countable and its chronological jump sizes summable
-- statement:
--   For any actual adapted dividend strategy, all strictly positive chronological right-payment jumps on [0,T], indexed directly by the source time type ℝ≥0 (including time zero), form a countable set with summable nonnegative payment sizes. This is the exact index type needed by the controlled signed Stieltjes correction theorem.
-- source:
--   04-B source right-atom support transport from real Stieltjes time to original nonnegative filtration time; prerequisite real-support d23b8276-0c22-4890-be0e-a327e910347a canonically Proved by 19759 before this publication retry

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_nnreal_countable_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ≥0 :=
      {t : ℝ≥0 | t ≤ T ∧ 0 < rightLimit D t ω - D t ω}
    A.Countable ∧
      Summable (fun t : A =>
        rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) := by
  sorry
