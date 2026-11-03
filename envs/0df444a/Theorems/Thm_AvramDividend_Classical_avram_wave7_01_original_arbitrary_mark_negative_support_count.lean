-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count
-- name    : AvramDividend.Classical.avram_wave7_01_original_arbitrary_mark_negative_support_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:21:55.220865+00:00
-- url     : https://prove2.me/theorems/c2e1a7f1-1187-4e21-9384-0ae2531dc181
-- title:
--   Original intrinsic jump count for arbitrary marks is carried by strictly negative marks
-- statement:
--   For every actual original spectrally negative Lévy path and every Borel mark set B, the literal source intrinsic jump measure on (s,t]×B equals its measure on (s,t]×(B∩(-∞,0)). This uses source pathwise nonpositive jump marks and the restriction to nonzero jumps, without changing Ω, P, 𝓕, X.X or X.ν and without assuming BV, finite activity or a compensator.
-- source:
--   Proved source jumpmark nonpositivity e95fe5bc-c756-43ca-82d7-acab7078e2eb and source intrinsic rectangle-to-encard f6336d40-2d19-444f-bacd-83724316de67.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_arbitrary_mark_negative_support_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) := by sorry
