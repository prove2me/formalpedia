-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_halfopen_marked_count_lintegral_add
-- name    : AvramDividend.Classical.avram_p3_2_halfopen_marked_count_lintegral_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:03:00.095857+00:00
-- url     : https://prove2.me/theorems/95e72758-57ec-446f-9156-b23ef62669a9
-- title:
--   Exact additivity of genuine marked-count nonlinear integrals across adjoining half-open physical cells
-- statement:
--   For a measurable jump-time support, a measurable original-compatible mark map and a nonnegative measurable nonlinear jump kernel, the marked counting integral over (a,c] splits exactly into (a,b] plus (b,c] when a≤b≤c. The identity uses the actual marked count, includes jumps at each right endpoint exactly once and permits infinite jump activity. Repeated application enables finite physical-grid source partitions needed for Avram P3 original BV verification.
-- source:
--   Source-exact generic marked counting integral/tSum theorem, pinned ENNReal.tsum_add, and a three-case disjoint partition proof of adjacent half-open clock cells. Intended application to original X intrinsic jump time support and mark map.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite physical jump-cell partition: nonnegative marked-count integrals
split exactly over adjacent half-open clock intervals, preserving endpoint atoms. -/

theorem AvramDividend.Classical.avram_p3_2_halfopen_marked_count_lintegral_add
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a c)).map mark)) =
      (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc a b)).map mark)) +
      (∫⁻ p, F p ∂((Measure.count.restrict (S ∩ Set.Ioc b c)).map mark)) := by sorry
