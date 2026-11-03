-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_negative_borel_mark_canonical_cutoff_exhaustion
-- name    : AvramDividend.Classical.avram_wave7_01_negative_borel_mark_canonical_cutoff_exhaustion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-03T00:12:48.635734+00:00
-- url     : https://prove2.me/theorems/585a7393-1047-48b5-abb8-c132971ad376
-- title:
--   Every strictly negative Borel mark set admits increasing measurable cutoffs separated from zero
-- statement:
--   For any measurable real mark set B strictly below zero, its intersections with the cutoffs (-∞,-1/(n+1)] form a measurable increasing sequence, each bounded a positive distance from zero, and their union is exactly B. This supplies an explicit admissible band exhaustion for extending the genuine original-process compensator by monotone convergence.
-- source:
--   Pinned Mathlib one_div_le_one_div_of_le, tendsto_one_div_add_atTop_nhds_zero_nat, iUnion_Iic_eq_Iio_of_lt_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_negative_borel_mark_canonical_cutoff_exhaustion
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      Monotone C ∧
      (⋃ n, C n) = B ∧
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε)) := by sorry
