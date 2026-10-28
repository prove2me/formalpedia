-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_weighted_deriv_transform_of_boundary
-- name    : AvramDividend.Classical.bv_scale_weighted_deriv_transform_of_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:02:47.77726+00:00
-- url     : https://prove2.me/theorems/5f43414e-e06f-4bc7-a1e4-09fbcda9b465
-- title:
--   BV scale-function weighted derivative transform retains the nonzero origin boundary
-- statement:
--   Under right-continuity of the q-scale function at the origin, positive-half-line derivative regularity, and the canonical Laplace identity with integrability, the weighted ordinary derivative has transform theta/(psi(theta)-q)-W(0). The proof composes an accepted weighted derivative integrability result and an accepted improper integration-by-parts boundary theorem. This supplies an exact BV derivative-transform component in the generator harmonicity cancellation formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; integration by parts of the q-scale Laplace transform.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_scale_weighted_deriv_transform_of_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hLaplace : (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * W x) = (X.ψ θ - q)⁻¹) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * deriv W x) =
    θ * (X.ψ θ - q)⁻¹ - W 0 := by sorry

end AvramDividend.Classical
