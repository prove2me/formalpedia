-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
-- name    : AvramDividend.Classical.chat07_scale_weighted_deriv_integrable_positive_halfline
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T21:52:48.585979+00:00
-- url     : https://prove2.me/theorems/a01f741d-18f2-4a06-af0d-61e118db667a
-- title:
--   Exponential half-line integrability of the derivative of a Lévy scale function
-- statement:
--   For a nonnegative Laplace argument θ at which the scale-function Laplace transform converges, the exponentially weighted ordinary derivative exp(-θx) W'(x) of the monotone q-scale function is integrable over the full positive half-line. The proof uses nonnegativity of the derivative, the proved adjacent-interval derivative/value comparison, finite telescoping, domination by the positive-halfline Laplace mass of W, and Mathlib's improper-integrability criterion. It does not assume global C1 or absolute continuity, and is a prerequisite for BV compensated-generator Fubini.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_weighted_deriv_integrable_positive_halfline
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ)) := by sorry
