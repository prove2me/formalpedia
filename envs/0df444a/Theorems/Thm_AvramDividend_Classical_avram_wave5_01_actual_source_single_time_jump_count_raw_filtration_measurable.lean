-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_single_time_jump_count_raw_filtration_measurable
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_single_time_jump_count_raw_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:00:41.934232+00:00
-- url     : https://prove2.me/theorems/f2fd10b9-0caf-4548-b05b-de690836b95d
-- title:
--   Original single-time Lévy marked jump count is measurable in the raw source filtration
-- statement:
--   For the actual original spectrally negative Levy process and each fixed t and Borel mark band B, the literal intrinsic singleton time atom count is measurable in the raw original filtration 𝓕 t. This uses the Proved raw-filtration source jump-mark adaptedness and pathwise singleton count identity, with no right-continuous or completed filtration replacement and no Poisson copy.
-- source:
--   Raw original adaptedness theorem 73fbc493 and exact singleton source count theorem 74f501cd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_single_time_jump_count_raw_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 t] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B)) := by sorry
