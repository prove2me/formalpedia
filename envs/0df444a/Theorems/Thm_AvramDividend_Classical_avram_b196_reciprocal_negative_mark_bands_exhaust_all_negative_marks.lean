-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
-- name    : AvramDividend.Classical.avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:35:36.741573+00:00
-- url     : https://prove2.me/theorems/2b7546bc-0e2f-4807-8daf-94a6a37759d2
-- title:
--   All strictly negative source jump marks are the union of increasing reciprocal negative cutoff bands
-- statement:
--   The original spectrally negative Lévy source reciprocal mark cutoffs used in the full marked jump Poisson analysis form an increasing family of negative real mark sets, with n-th band consisting of all marks up to the negative reciprocal of n plus one. The union of these cutoff mark sets is exactly the set of all strictly negative real marks. Every mark in a cutoff band is negative because the reciprocal is positive. Conversely every negative mark is eventually above the negative reciprocal cutoff because the reciprocal of n plus one tends to zero, so some band includes it. This exact set equality is the primary missing geometric input to reconstruct the original full negative marked source Poisson count as the increasing supremum of finite reciprocal cutoff band counts, establish its a.e. measurability and combine with the Proved mix_fin14 finite expected count to prove almost-sure finiteness, without assuming global all-path finite activity.
-- source:
--   Mathlib tendsto_one_div_add_atTop_nhds_zero_nat, open Iio event and countable union membership.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The increasing original reciprocal negative mark bands exhaust exactly the strictly negative real marks. -/

theorem AvramDividend.Classical.avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks :
    (⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1)))) =
      Iio (0 : ℝ) := by sorry
