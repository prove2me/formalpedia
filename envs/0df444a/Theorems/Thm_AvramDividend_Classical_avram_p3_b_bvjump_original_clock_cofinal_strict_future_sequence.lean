-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:37:24.329488+00:00
-- url     : https://prove2.me/theorems/cd613320-c61a-4911-bca3-9b7909ea248d
-- title:
--   Original nonnegative-real clock has a decreasing strictly future cofinal sequence
-- statement:
--   For each original physical time i∈NNReal, produce a strictly later decreasing countable clock r_n approaching i from the right, in the exact cofinality formulation required for the P3-B right-continuous marked-measure extension. No auxiliary probability space or jump assumptions.
-- source:
--   Mathlib.Topology.Order.IsLUB exists_seq_strictAnti_tendsto, Iio_mem_nhds and Filter.Eventually.exists.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
    (i : ℝ≥0) :
    ∃ r : ℕ → ℝ≥0,
      Antitone r ∧ (∀ n, i < r n) ∧
        (∀ u : ℝ≥0, i < u → ∃ n, r n < u) := by sorry
