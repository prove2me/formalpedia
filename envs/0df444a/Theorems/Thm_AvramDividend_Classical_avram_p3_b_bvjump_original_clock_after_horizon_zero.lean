-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_zero
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:38:07.169799+00:00
-- url     : https://prove2.me/theorems/545103b7-ded5-4833-9f68-a900c57713b1
-- title:
--   Genuine stopped original physical clock has zero mass after its horizon
-- statement:
--   The actual real-Lebesgue clock stopped at [0,T] and mapped to nonnegative physical time has exactly zero mass for any later interval (s,t] with T≤s, including all empty endpoint cases. The proof uses the genuine map and restriction of measures and the source-clock preimage disjointness, and needs no Lévy first moment or compensator axiom.
-- source:
--   P3-B original clock preimage empty lemma; Mathlib Measure.map_apply, Measure.restrict_apply, measure_empty.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_zero
    (s t T : ℝ≥0) (hTs : T ≤ s) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) = 0 := by sorry
