-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_raw_large_cutoff_unit_partition
-- name    : AvramDividend.Classical.avram_p4_c_generator_raw_large_cutoff_unit_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:55:36.685594+00:00
-- url     : https://prove2.me/theorems/df2f07b8-e2d1-4857-8e80-7ef48fcb72b4
-- title:
--   Original epsilon-truncated uncompensated negative jump integral partitions exactly at source unit atom
-- statement:
--   For 0<epsilon<1 and original GeneratorIntegrable w y, the uncorrected payoff jump integral over all z<-epsilon is exactly the sum over z≤-1 and -1<z<-epsilon, with absolute integrability established individually, disjoint sets, and the z=-1 atom retained in the large band.
-- source:
--   source generatorIntegrand_large_negative_integrable and P4-C finite_band_raw_integrable

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_raw_large_cutoff_unit_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (-ε), w (y + z) - w y ∂X.ν) =
      (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) := by sorry
