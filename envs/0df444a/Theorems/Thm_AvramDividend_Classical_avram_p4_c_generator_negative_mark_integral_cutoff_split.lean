-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split
-- name    : AvramDividend.Classical.avram_p4_c_generator_negative_mark_integral_cutoff_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:52:51.325736+00:00
-- url     : https://prove2.me/theorems/5434bf03-5ab7-4955-984e-cb4aa16c7af7
-- title:
--   Original generator compensated Lévy integral splits at every strictly positive jump cutoff
-- statement:
--   For every ε>0, the original generator domain gives ν-integrability on both exactly disjoint bands z<-ε and -ε≤z<0. These bands partition all negative source marks, so the full original compensated jump integral equals the sum of its large-mark and small-mark integrals without changing truncation, losing the boundary z=-ε, or postulating extra jump-tail moments. This is the reusable ε-cutoff Lévy generator bridge required for Itô–Meyer truncation.
-- source:
--   Authoritative SpectrallyNegativeLevy.GeneratorIntegrable, generatorIntegrand and generator definitions; Avram–Palmowski–Pistorius p.20 generator convention and Proposition 4(i). The existing Proved generatorIntegral_negative_jump_partition treats only the fixed threshold 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_negative_mark_integral_cutoff_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      (∫ z in Ico (-ε) 0, SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
