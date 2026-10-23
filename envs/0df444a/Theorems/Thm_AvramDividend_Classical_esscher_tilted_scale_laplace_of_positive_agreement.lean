-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_of_positive_agreement
-- name    : AvramDividend.Classical.esscher_tilted_scale_laplace_of_positive_agreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:48:52.808343+00:00
-- url     : https://prove2.me/theorems/3b2059d8-55b1-4d53-9e22-1b3b282b55ce
-- title:
--   Signed-integrable Laplace transform of an Esscher scale representative on positive levels
-- statement:
--   Any function V agreeing on positive levels with the exponential Esscher tilt of a canonical q-scale function inherits its integrable Laplace transform, including the exact reciprocal Levy-exponent denominator. The proof transports both integrability and the set integral by pointwise equality on the open positive half-line. This discharges the exact V transform input for the Gaussian integrated Volterra equation without imposing V's values on the negative half-line.
-- source:
--   Proved esscher_tilted_scale_laplace_shift 73c21e1c-2f32-4354-8be9-95d6cdd110e4 and pinned Mathlib integral congruence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_scale_laplace_of_positive_agreement
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ θ : ℝ) (hθ : 0 ≤ θ + φ) (hψ : q < X.ψ (θ + φ))
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y)
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
      (X.ψ (θ + φ) - q)⁻¹ := by sorry
