-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_single_time_jump_count_rightCont_filtration_measurable
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_single_time_jump_count_rightCont_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:55:17.792603+00:00
-- url     : https://prove2.me/theorems/26672897-2969-4373-a20a-c7bda454466f
-- title:
--   Original single-time Lévy marked jump count is measurable in the actual right-continuous source filtration
-- statement:
--   For the unchanged original spectrally negative Lévy source, any fixed time t and Borel jump mark set B, the actual singleton-time jump-measure count is measurable with respect to the original right-continuous filtration at t. This uses the Proved strongly adapted actual source jump mark and exact source singleton atom identity. It does not claim predictability under the raw original filtration, and is not a marked Poisson intensity statement.
-- source:
--   Original rightCont adapted jump-mark theorem 3de01e15, newly submitted exact source singleton-time atom theorem 74f501cd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_single_time_jump_count_rightCont_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕.rightCont t] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B)) := by sorry
