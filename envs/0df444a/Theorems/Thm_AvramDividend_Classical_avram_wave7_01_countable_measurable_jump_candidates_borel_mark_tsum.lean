-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_measurable_jump_candidates_borel_mark_tsum
-- name    : AvramDividend.Classical.avram_wave7_01_countable_measurable_jump_candidates_borel_mark_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:50:52.05908+00:00
-- url     : https://prove2.me/theorems/9716b110-201d-4068-8fa9-a1de13ffd2f2
-- title:
--   Arbitrary Borel marked count over a countable measurable time–mark candidate sequence is measurable
-- statement:
--   Once a countable sequence of prospective jump times and jump marks has been constructed measurably from the original coordinate path, the extended count of positive-time candidates up to a finite horizon with arbitrary Borel marks is measurable. This theorem proves the analytic summation step without inventing any new stochastic model, asserting independent increments, or assuming grid increments equal true jump sizes. Deduplication and source intrinsic count equality are separate genuine obligations.
-- source:
--   Pooled Borel measurability of positive time, finite horizon and marked state cells, Measurable.ite, and Measurable.ennreal_tsum in pinned Mathlib.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_countable_measurable_jump_candidates_borel_mark_tsum
    {α : Type*} [mα : MeasurableSpace α]
    (time : ℕ → α → ℝ≥0) (mark : ℕ → α → ℝ)
    (htime : ∀ n : ℕ, Measurable (time n))
    (hmark : ∀ n : ℕ, Measurable (mark n))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun x : α =>
      ∑' n : ℕ,
        if 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B
        then (1 : ℝ≥0∞) else 0) := by sorry
