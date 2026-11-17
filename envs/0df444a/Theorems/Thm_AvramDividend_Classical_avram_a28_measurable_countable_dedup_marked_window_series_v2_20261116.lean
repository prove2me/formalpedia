-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
-- name    : AvramDividend.Classical.avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:37:51.691201+00:00
-- url     : https://prove2.me/theorems/8ae03379-c530-4994-b20b-8758749145f4
-- title:
--   A countable deduplicated Borel marked-jump series is measurable for any half-open time window
-- statement:
--   Given a countable family of jointly measurable jump candidate times and measurable marks on real-valued paths, the series counting first occurrences whose times fall in (s,T] and whose marks lie in a measurable Borel set is a measurable ENNReal function on the original product-coordinate path space. Establish measurable time thresholds, mark membership, countable distinctness predicate and apply measurable_tsum. This lemma is the missing time-window counterpart of the Proved candidate count construction used for original path adaptedness.
-- source:
--   Pinned Mathlib measurableSet_lt/le, measurableSet_eq_fun and Measurable.tsum.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hmark : ∀ k, Measurable (mark k)) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑' k : ℕ,
        if s < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (1 : ℝ≥0∞) else 0) := by sorry
