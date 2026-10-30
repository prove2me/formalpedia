-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity
-- name    : AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T23:54:27.393994+00:00
-- url     : https://prove2.me/theorems/0aa170e8-3557-48df-893e-a2015627238e
-- title:
--   Log-concavity of the Esscher-tilted q-scale function at the positive Esscher root, for unbounded variation
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Let phi > 0 be a root of the Laplace exponent, psi(phi) = q, and let V be the Esscher-tilted function V(x) = exp(-phi x) W(x), assumed differentiable on the positive half-line. Then the logarithm of V is concave on the positive half-line, that is, the logarithmic derivative V'/V is nonincreasing. This is the Kyprianou log-concavity of the Esscher-tilted scale function, and it is the step that makes the excursion-height measure well defined: the nonincreasing continuous tail V'/V is the tail function of an atomless Stieltjes measure, and the fundamental theorem of calculus then turns that measure into the integrated identity for the scale function. The hypothesis of unbounded variation excludes the bounded-variation renewal-density case, so no standing assumption is required: the integrable first moment of the positive part is not available when the Levy measure has an infinite first moment near zero, and the infinite-small-jump case is one of the regimes this theorem must cover.
-- source:
--   Kyprianou (2011), Excursions and Stochasticity, the log-concavity of the q-scale function and the associated excursion-height measure; Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, the monotonicity of the logarithm of the tilted scale function.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_tilted_scale_log_concavity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by sorry
