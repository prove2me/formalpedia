-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116
-- name    : AvramDividend.Classical.avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:32:47.581199+00:00
-- url     : https://prove2.me/theorems/fde6db0d-2584-4743-ae54-d76ab9dee830
-- title:
--   Measurable original extended-nonnegative count has nonzero probability equal to complement of its void probability
-- statement:
--   For any measurable ENNReal-valued count on the original probability space, the event that the count is nonzero is the measurable complement of its void event. Thus its real probability is one minus the void real probability. This fixes the missing measurable-singleton assumption in an earlier attempted too-general lemma and applies directly to the actual physical marked-jump count, without changing source.
-- source:
--   Mathlib probability measure complement and ENNReal.toReal_sub_of_le; Borel singleton {0} is measurable for ENNReal.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_ENNReal_count_nonzero_probability_complement_20261116
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Ω → ℝ≥0∞) (hC : Measurable C) :
    (P {ω : Ω | C ω ≠ 0}).toReal =
      1 - (P {ω : Ω | C ω = 0}).toReal := by sorry
