-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_laplace_compensated_jump_boundary
-- name    : AvramDividend.Classical.scaleFunction_laplace_compensated_jump_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:35:11.976637+00:00
-- url     : https://prove2.me/theorems/89e22056-d7b2-4dcc-9f7f-959e8fa6c9ba
-- title:
--   Correct origin boundary term in the compensated single-jump Laplace transform
-- statement:
--   Let W be a q-scale function, differentiable on the positive real half-line and right-continuous at the origin, with integrable exponentially weighted derivative. For each nonpositive jump y and theta≥0 with psi(theta)>q, the Laplace transform of its fully compensated Lévy generator increment equals (exp(theta*y)-1-theta*y*1_{(-1,1)}(y))/(psi(theta)-q) + y*1_{(-1,1)}(y)*W(0). This is obtained by substituting the proved weighted derivative transform with its essential origin boundary term into the proved fixed-jump compensation formula. The expression is a pointwise-in-y identity, with the compensated exponential numerator kept intact to preserve finite integrability when the Lévy first moment diverges.
-- source:
--   The compensated Lévy–Khintchine exponential and the scale-function integration-by-parts boundary formula, for the generator q-harmonicity analysis of Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_laplace_compensated_jump_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         SpectrallyNegativeLevy.generatorIntegrand W x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
          (X.ψ θ - q)⁻¹ +
       (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) * W 0 := by sorry

end AvramDividend.Classical
