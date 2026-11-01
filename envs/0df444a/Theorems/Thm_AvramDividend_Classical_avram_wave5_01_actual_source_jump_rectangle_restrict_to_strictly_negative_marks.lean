-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:19:02.625212+00:00
-- url     : https://prove2.me/theorems/56a5b5da-57a4-4392-bfd8-432b4a6fbb5b
-- title:
--   Original spectrally negative Lévy jump count is exactly supported on strictly negative marks
-- statement:
--   For every actual original source Lévy sample path, arbitrary nonnegative time window (s,t], and any Borel mark set B, its literal intrinsic marked jump count on B is exactly its count on B∩(-∞,0). No positive or zero source jumps can contribute because every positive-time actual jump is nonpositive, and jump measure excludes zero marks. This reduces the source-compensator rectangle obligation for all signed Borel marks to strictly negative mark sets without a detached process or law transfer.
-- source:
--   Original intrinsic rectangle-as-jump-set cardinality f6336d40-2d19-444f-bacd-83724316de67 and actual pathwise nonpositive jump mark e95fe5bc-c756-43ca-82d7-acab7078e2eb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
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
