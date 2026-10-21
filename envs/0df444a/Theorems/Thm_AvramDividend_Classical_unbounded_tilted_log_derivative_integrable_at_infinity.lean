-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_log_derivative_integrable_at_infinity
-- name    : AvramDividend.Classical.unbounded_tilted_log_derivative_integrable_at_infinity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T23:07:39.460624+00:00
-- url     : https://prove2.me/theorems/64de16a8-bef0-43de-bf0e-fe0df0ad2419
-- title:
--   Flat tail of the logarithmic derivative of the Esscher-tilted q-scale function, for unbounded variation
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Let phi > 0 be a root of the Laplace exponent, psi(phi) = q, and let V be the Esscher-tilted function V(x) = exp(-phi x) W(x), assumed differentiable on the positive half-line. Then there is a positive measure mu on the positive half-line whose tail at level x is the tail integral of the logarithmic derivative of V, namely mu([x, infinity)) = integral over (0, infinity) of V'(y)/V(y). The hypothesis of unbounded variation is exactly what excludes the bounded-variation renewal-density case, so no standing assumption is required: the integrable first moment of the positive part is not available when the Levy measure has an infinite first moment near zero, and the infinite-small-jump case is one of the regimes this theorem must cover. This is the flat-tail condition on the logarithmic derivative: it says that the log-derivative of the tilted function is integrable at infinity, so the excursion intensity above each level is finite. Together with the absolute continuity of the tilted function it yields the excursion representation of the q-scale function, in which the tilted function is determined by the excursion-height measure.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, the excursion formula (5) and the flat-tail condition; Kuznetsov, Kyprianou, Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, the finiteness of the excursion intensity above each level.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_tilted_log_derivative_integrable_at_infinity
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
    ∃ (μ : Measure ℝ),
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        μ.real (Ici x) = ∫ y in Ioi (0 : ℝ), (deriv V y / V y) ∂volume) := by sorry
