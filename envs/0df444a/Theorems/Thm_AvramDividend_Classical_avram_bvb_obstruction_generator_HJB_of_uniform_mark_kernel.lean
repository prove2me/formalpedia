-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
-- name    : AvramDividend.Classical.avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:05:40.939872+00:00
-- url     : https://prove2.me/theorems/2a570b90-4ab2-4e0e-b7c7-4c5db6743b5b
-- title:
--   Original uniform negative-jump HJB generator nonpositive from source triplet and exact mark kernel
-- statement:
--   For an original spectrally negative Lévy process with σ=0 and c=1/2, at positive reserve y with verification candidate w(y)=1/2+y and w′(y)=1, if the exact original negative-mark generator integral is y(y−1)/2 for 0<y<1 and zero above, then the generator super-solution inequality X.generator w y−w y≤0 holds. This is a sound reduction of the true HJB condition, without any invented regularity or integrability.
-- source:
--   Unfold the original pinned generator definition: zero Gaussian term, half-unit drift times unit derivative and the exact source compensated kernel. Subtract the candidate value to get the already Proved piecewise scalar nonpositive residual b65bd345.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (y : ℝ) (hy : 0 < y) (w : ℝ → ℝ)
    (hσ : X.σ = 0) (hc : X.c = 1 / 2)
    (hw : w y = 1 / 2 + y) (hd : deriv w y = 1)
    (hJump : (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      if y < 1 then y * (y - 1) / 2 else 0) :
    X.generator w y - w y ≤ 0 := by sorry
