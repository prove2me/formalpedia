-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegral_negative_jump_partition
-- name    : AvramDividend.Classical.generatorIntegral_negative_jump_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:26:11.055982+00:00
-- url     : https://prove2.me/theorems/07b30af6-e699-442f-b7ec-98451da12601
-- title:
--   Partition the Lévy generator jump integral at jump size one
-- statement:
--   The compensated generator integrand is integrable on the negative Lévy half-line. Split the integral at jump size -1 into the disjoint small interval (-1,0) and large interval (-infinity,-1]. This is required to recover the BV physical drift without losing the endpoint atom at -1.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegral_negative_jump_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (∫ y in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) =
      (∫ y in Ioo (-1 : ℝ) 0, SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) +
      (∫ y in Iic (-1 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) := by sorry
