-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T01:06:28.575186+00:00
-- url     : https://prove2.me/theorems/2979e9ec-ef8e-4708-841f-11dbb6d1fac0
-- title:
--   Exact original uniform-negative Levy compensated generator integral of half-unit affine candidate
-- statement:
--   For original spectrally negative Lévy measure equal to volume restricted to (-1,0), candidate w(u)=0 below zero and 1/2+u otherwise, with derivative one at positive reserve y, the complete original negative-jump generator integral is y(y−1)/2 for 0<y<1 and zero for y≥1. This discharges the explicit source kernel hypothesis in the original uniform-triplet HJB lemma.
-- source:
--   Restrict original ν to negative unit marks, apply exact pointwise original generatorIntegrand crossing identity, then apply Proved full uniform compensated kernel integral f98142c5. The integrability is finite because support is bounded and ν has mass 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (y : ℝ) (hy : 0 < y) (w : ℝ → ℝ)
    (hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u)
    (hd : deriv w y = 1) :
    (∫ z in Iio (0 : ℝ),
       SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      if y < 1 then y * (y - 1) / 2 else 0 := by sorry
