-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:19:01.459504+00:00
-- url     : https://prove2.me/theorems/01470a72-0863-4b77-8ab9-cd20cb03d739
-- title:
--   Unbounded-variation original q-scale primitive has both zero-origin Laplace boundary terms
-- statement:
--   For the actual positive-discount q-scale of an unbounded-variation spectrally negative Lévy process, U(x)=∫_0^x W(t)dt satisfies U(0)=0 and U'(0)=0. The second identity is not assumed: it derives from the Proved true W(0)=0 and global scale continuity in unbounded variation via pinned interval-integral FTC at zero. These are the exact two lower-boundary terms needed to Laplace transform the original Lévy generator applied to the primitive without a false Gaussian derivative or BV boundary assumption.
-- source:
--   Avram Palmowski Pistorius (2007), scale function at zero and original generator; Proved c1b8958a and 3321ae26; Mathlib intervalIntegral.integral_hasDerivAt_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_zero_origin_value_and_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫ t in (0 : ℝ)..(0 : ℝ), W t) = 0 ∧
      deriv (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) 0 = 0 := by sorry
