-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_shifted_laplace_transform
-- name    : AvramDividend.Classical.scaleFunction_shifted_laplace_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:35:49.696347+00:00
-- url     : https://prove2.me/theorems/bd4aafe1-326f-4d09-9f6f-d21fab46ce63
-- title:
--   Laplace transform of a scale function after a nonpositive spatial shift
-- statement:
--   For a q-scale function W supported on [0,infinity), theta>=0 satisfying psi(theta)>q, and nonpositive y, one has ∫_{x>0} exp(-theta*x)W(x+y) dx = exp(theta*y)/(psi(theta)-q). The proof uses full-line Lebesgue translation invariance, zero support below the origin even after a nonpositive shift, and the defining Laplace-transform identity of IsScaleFunction. It is the exact fixed-jump spatial translation term used in the compensated Levy-generator transform.
-- source:
--   Scale-function Laplace transform (3.4) and elementary change of variables in Avram, Palmowski and Pistorius (2007), employed in the generator harmonicity argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_shifted_laplace_transform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W (x + y)) =
      Real.exp (θ * y) * (X.ψ θ - q)⁻¹ := by sorry

end AvramDividend.Classical
