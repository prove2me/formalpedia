-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_zero_initial_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:07:00.222809+00:00
-- url     : https://prove2.me/theorems/e2216ed6-948c-45f0-8cab-535d1fae6860
-- title:
--   Original Lévy jump measure has no mass at initial time, pathwise
-- statement:
--   For every actual SpectrallyNegativeLevy P 𝓕 sample path and every Borel jump-mark band B, the intrinsic source jump measure gives zero mass to {0}×B. The source jump measure counts only strictly positive times. This discharges the source time-zero boundary component needed by the proved σ-finite predictable compensator uniqueness lemma 85791e69-1071-4a55-a3a3-c402870c4066, without replacing the process or filtration.
-- source:
--   Exact original intrinsic jump measure and measurable original jump mark, source 9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1. Time-zero boundary hBot for P1 source compensator uniqueness 85791e69-1071-4a55-a3a3-c402870c4066.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_zero_initial_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({(0 : ℝ≥0)} ×ˢ B) = 0 := by sorry
