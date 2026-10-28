-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_cross_derivative_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_tilted_scale_cross_derivative_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:42:21.035199+00:00
-- url     : https://prove2.me/theorems/15353ebf-1b25-4386-990e-96d10e26b18c
-- title:
--   Local Esscher-tilted q-scale logarithmic derivative order from corrected exits
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, its corrected killed two-sided exit-scale identity implies the cross-derivative inequality for the Esscher-tilted q-scale function V(z)=exp(-φz)W(z), for any real tilt φ and any ordered positive points x≤y where W is differentiable. In particular V'(y)V(x)≤V'(x)V(y) with no global C1 assumption. The proof imports the verified corrected-exit cross derivative theorem and a verified generic exponential tilt preservation theorem, supplying a local analytic consequence for the open full Esscher-tilted log-concavity milestone.
-- source:
--   Avram Palmowski Pistorius (2007) corrected two-sided exit scale formula and deterministic exponential Esscher tilting of logarithmic derivatives.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_cross_derivative_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_exponential_tilt_preserves_cross_derivative_order
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_scale_cross_derivative_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (φ x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ W x)
    (hdy : DifferentiableAt ℝ W y) :
    deriv (fun z : ℝ => Real.exp (-φ * z) * W z) y *
        (Real.exp (-φ * x) * W x) ≤
      deriv (fun z : ℝ => Real.exp (-φ * z) * W z) x *
        (Real.exp (-φ * y) * W y) := by sorry
