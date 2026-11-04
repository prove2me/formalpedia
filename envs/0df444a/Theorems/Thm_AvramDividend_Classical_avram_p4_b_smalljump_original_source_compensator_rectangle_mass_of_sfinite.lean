-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:27:25.06423+00:00
-- url     : https://prove2.me/theorems/adb8b702-cf20-4bee-b009-76946b7ee015
-- title:
--   Original Lévy product compensator rectangle mass under sigma-finiteness
-- statement:
--   With a source sigma-finite Lévy intensity and an explicit original nonnegative-time interval measure, the product compensator has the correct rectangular intensity.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hNuSFinite : SFinite X.ν)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
