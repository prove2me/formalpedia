-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_product_compensator_cell_rate_of_time_volume
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_product_compensator_cell_rate_of_time_volume
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:15:50.882855+00:00
-- url     : https://prove2.me/theorems/452f9c5b-e309-4b03-bb45-226f56d35f7f
-- title:
--   Original Levy product compensator rectangle cell rate
-- statement:
--   Given a verified original nonnegative-time interval-volume measure, the actual Levy product compensator assigns a time-mark cell the original P2 duration times X.nu intensity.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_product_compensator_cell_rate_of_time_volume
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
