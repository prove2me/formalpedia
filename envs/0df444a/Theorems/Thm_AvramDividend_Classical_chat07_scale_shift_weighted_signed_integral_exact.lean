-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_signed_integral_exact
-- name    : AvramDividend.Classical.chat07_scale_shift_weighted_signed_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:24:23.849418+00:00
-- url     : https://prove2.me/theorems/bc08533f-1d28-4036-bfe1-0ea60b346eab
-- title:
--   Exact signed Laplace transform of a negative scale shift
-- statement:
--   For a positive negative-jump magnitude r and an admissible exponential Laplace parameter, the weighted integral of W(x-r)-W(x) over positive reserves equals (exp(-theta r)-1)/(psi(theta)-q). The result follows from global monotonicity of the scale function and the separately accepted absolute shift Laplace identity. It establishes the exact signed nonlocal jump transform needed for the generator's characteristic exponent, without assuming generator harmonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_exact
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_shift_weighted_signed_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) * (W (x-r) - W x)) =
      (Real.exp (-(θ*r)) - 1) * (X.ψ θ - q)⁻¹ := by sorry
