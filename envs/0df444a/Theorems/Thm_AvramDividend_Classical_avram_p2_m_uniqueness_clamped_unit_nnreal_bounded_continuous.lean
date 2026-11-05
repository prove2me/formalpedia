-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:23:30.552903+00:00
-- url     : https://prove2.me/theorems/87d3135c-5d81-4659-ad12-fe7d1427034b
-- title:
--   Globally bounded NNReal test extension of the unit-interval identity
-- statement:
--   There is a bounded continuous nonnegative real-valued test function on the entire real line with values at most one whose ENNReal embedding agrees with ENNReal.ofReal z on the unit interval. This constructs the exact compactifying test required to transfer original small-time unit-support moment limits through weak cluster points.

import Mathlib
open MeasureTheory Set Topology BoundedContinuousFunction
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_clamped_unit_nnreal_bounded_continuous :
    ∃ f : ℝ →ᵇ ℝ≥0,
      (∀ z : ℝ, f z ≤ 1) ∧
      ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
        (f z : ℝ≥0∞) = ENNReal.ofReal z := by sorry
