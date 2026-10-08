-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
-- name    : AvramDividend.Classical.scaleFunction_tilted_positive_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:17:30.028525+00:00
-- url     : https://prove2.me/theorems/7654d06e-e154-470e-9ba9-8543413cf98d
-- title:
--   The tilted scale function has the canonical positive Laplace lintegral
-- statement:
--   Let W be the q-scale function of X. For real s and φ such that θ=s+φ is nonnegative and ψ(θ)>q, the positive extended-real Laplace integral of exp(-s x) exp(-φ x) W(x) over x>0 equals ENNReal.ofReal((ψ(θ)-q)^(-1)). This is the ENNReal form of the defining real Laplace-transform identity for W. The proof uses the IsScaleFunction integrability/equality, nonnegativity of W on the positive half-line, and the exact algebra exp(-s x)exp(-φ x)=exp(-(s+φ)x).
-- source:
--   Canonical IsScaleFunction definition in AvramDividend_Classical_ScaleFunction plus pinned Mathlib ofReal_integral_eq_lintegral_ofReal and ae_restrict_mem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_tilted_positive_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s φ : ℝ) (hθ0 : 0 ≤ s + φ) (hψ : q < X.ψ (s + φ)) :
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal
        (Real.exp (-s * x) * (Real.exp (-φ * x) * W x))) =
      ENNReal.ofReal ((X.ψ (s + φ) - q)⁻¹) := by sorry
