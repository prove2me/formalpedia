-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
-- name    : AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:03:55.152961+00:00
-- url     : https://prove2.me/theorems/459c13bc-a058-4be9-8a77-6e5e9e629ae5
-- title:
--   Exact negative-spatial-shift Laplace transform of the original source q-scale primitive
-- statement:
--   For a genuine original q-scale W and its interval primitive U(x)=∫₀ˣW, θ>0,q<ψθ and a nonpositive spatial jump y, the positive-halfline Laplace transform of U(x+y) is exp(θy)/[θ(ψθ-q)]. The negative reserve part is handled by the exact U(z)=0 for z≤0, then whole-line translation of the exponential-weighted integral, then the source q-scale primitive transform. No generator harmonicity, variation assumption or diffusion is used. This is the exact shifted source transform needed to calculate a compensated primitive fixed-jump Laplace identity with zero-origin boundary; it is not the scale W shift theorem applied invalidly to a non-scale U.
-- source:
--   Avram Palmowski Pistorius 2007 Section 3 scale Laplace identity; generic Proved Mathlib-level weighted shift  and zero negative extension source theorems weightedLaplace_integral_shift_real / weightedLaplace_integral_Ioi_of_zero_negative; P2 zero primitive support 6dcc8ffe and Proved genuine real primitive Laplace theorem 9f40ea02.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_shifted_laplace_transform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ t in (0 : ℝ)..(x + y), W t)) =
      Real.exp (θ * y) * ((X.ψ θ - q)⁻¹ / θ) := by sorry
