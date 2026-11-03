-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:53:21.545214+00:00
-- url     : https://prove2.me/theorems/73b70a4a-e3cc-4139-9e84-42a8afac497e
-- title:
--   First-occurrence deduplicated arbitrary Borel jump candidate count is measurable
-- statement:
--   For measurable indexed candidate jump times and candidate real marks, count each positive-time candidate at most once, retaining only its first index, and filter its mark by any Borel set. The resulting ENNReal count up to a fixed horizon is measurable, even when the candidates collide or the count is infinite. This is the deduplication ingredient needed after countable rational first-downcrossing enumeration of actual source Lévy negative jumps. Equality of the candidate enumeration to the intrinsic source jump measure still requires identifying the genuine left and right jump sizes.
-- source:
--   Finite intersections of Borel marked-time events, countable intersections of pairwise time-inequality events using measurableSet_eq_fun, and Measurable.ennreal_tsum.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
    {α : Type*} [mα : MeasurableSpace α]
    (time : ℕ → α → ℝ≥0) (mark : ℕ → α → ℝ)
    (htime : ∀ n : ℕ, Measurable (time n))
    (hmark : ∀ n : ℕ, Measurable (mark n))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun x : α =>
      ∑' n : ℕ,
        if 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B ∧
          (∀ j : ℕ, j < n → time j x ≠ time n x)
        then (1 : ℝ≥0∞) else 0) := by sorry
