-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_deriv_bounded_near_zero
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_deriv_bounded_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T01:25:35.270407+00:00
-- url     : https://prove2.me/theorems/afcf6529-6af4-4fc8-8c4f-e8d450d25c1e
-- title:
--   Original Gaussian scale derivative is uniformly bounded on the first positive unit interval
-- statement:
--   For any original spectrally negative Lévy source with Standing, q>0, a genuine q-scale function and positive Gaussian coefficient, there is a nonnegative constant bounding the absolute ordinary derivative of the scale function at every reserve 0<x≤1. Use the accepted right-continuous extension at zero, the genuine Gaussian C2 result and compactness of [0,1]. This source theorem permits a linear pointwise origin-crossing jump bound to become a quadratic integrated strip bound without falsely identifying deriv W 0 with 2/σ².
-- source:
--   Avram–Palmowski–Pistorius (2007), Gaussian scale origin regularity; accepted source Gaussian C2, zero origin and corrected right-derivative extension; Mathlib compact continuous image boundedness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_right_continuous_extension

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_deriv_bounded_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, |deriv W x| ≤ C := by sorry
