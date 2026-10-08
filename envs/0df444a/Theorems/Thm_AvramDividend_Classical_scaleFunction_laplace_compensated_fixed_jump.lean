-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_fixed_jump
-- name    : AvramDividend.Classical.scaleFunction_laplace_compensated_fixed_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:07:22.30037+00:00
-- url     : https://prove2.me/theorems/95578a14-828d-48da-8f51-69c39fe56527
-- title:
--   Laplace transform of a single compensated negative Lévy jump of the scale function
-- statement:
--   For a nonpositive jump y and parameter θ≥0 satisfying ψ(θ)>q, if the exponentially weighted scale-function derivative is integrable on the positive half-line, then the Laplace transform in x of the full compensated generator increment W(x+y)-W(x)-W'(x)y 1_{(-1,1)}(y) equals (e^(θy)-1)/(ψ(θ)-q) minus y 1_{(-1,1)}(y) times the weighted integral of W'. This follows by splitting in the state variable x (where each fixed-y term is separately integrable), using the already proved negative-increment Laplace theorem, and factoring the constant compensation coefficient. This does not split an integral across the Lévy measure and therefore remains sound even when ν has infinite small-jump first moment.
-- source:
--   Compensated fixed-jump integrand identity used in a rigorous Lévy-generator Laplace transform, derived from scale-function transforms and ordinary integrable function linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_compensated_fixed_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hder : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1) * (X.ψ θ - q)⁻¹ -
        (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) *
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv W x) := by sorry

end AvramDividend.Classical
