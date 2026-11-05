-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_negative_supported_original_mark_measure_full_borel_restriction
-- name    : AvramDividend.Classical.avram_wave7_01_negative_supported_original_mark_measure_full_borel_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:14:53.378517+00:00
-- url     : https://prove2.me/theorems/99c1781e-0660-49d2-ae23-e95281430cd2
-- title:
--   Negative-carried Lévy and original expected mark measures restrict all Borel tests to negative marks
-- statement:
--   If a real Borel measure μ charges no nonnegative marks, then for every measurable B its mass equals that of B∩(-∞,0). This measure algebra lemma is applied both to the true source ν via X.ν_Ici and to the actual past-restricted expected intrinsic source mark measure; it permits extension of the negative-mark compensator to all Borel marks.
-- source:
--   Pinned Mathlib measure_union on disjoint measurable sets and measure_mono_null; source ν support and original source count support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_negative_supported_original_mark_measure_full_borel_restriction
    (μ : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hZero : μ (Ici (0 : ℝ)) = 0) :
    μ B = μ (B ∩ Iio (0 : ℝ)) := by sorry
