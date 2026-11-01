-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:33:45.782187+00:00
-- url     : https://prove2.me/theorems/a9a01dd4-244b-447b-b04b-4f97b1fb8c57
-- title:
--   Global differentiability of the actual unbounded-variation scale primitive
-- statement:
--   In the actual q>0 unbounded-variation source Lévy branch (not BV), the oriented primitive U(x)=∫_0^x W has derivative exactly W at **all** real x. At x>0 this uses the genuine source FTC theorem, at x<0 both the primitive and scale vanish on an open neighbourhood, and at x=0 it uses the independently Proved zero-boundary lemma 01470a72 and W(0)=0. This supplies global U C1/compensation measurability and the correct boundary derivative for the eventual full non-Gaussian generator Laplace transform. It is false without ¬BV because the zero-extended W can jump at origin, so the explicit assumption is essential.
-- source:
--   Avram Palmowski Pistorius 2007, scale primitive and true origin; P2 01470a72, 6dcc8ffe, source FTC scaleFunction_primitive_deriv_positive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    deriv (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) = W := by sorry
