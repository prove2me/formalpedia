-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_cutoff_unit_partition
-- name    : AvramDividend.Classical.avram_p4_c_generator_large_cutoff_unit_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:41:55.354263+00:00
-- url     : https://prove2.me/theorems/351f6fbb-aa5d-4997-958c-af3f5a55643e
-- title:
--   Original epsilon-large negative jumps split into the full untruncated z≤−1 tail and the finite compensated annulus
-- statement:
--   For original source generator integrability and a strict cutoff 0<epsilon<1, split the epsilon-large negative jump band z<-epsilon into exactly disjoint z<=-1 and -1<z<-epsilon. The -1 atom is retained in the uncompensated large-jump set; both terms are independently integrable by mono_set from the original GeneratorIntegrable source domain.
-- source:
--   SpectrallyNegativeLevy.GeneratorIntegrable and generatorIntegrand; original generator strict-unit truncation, paper Eq (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_large_cutoff_unit_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (∫ z in Iic (-1 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
