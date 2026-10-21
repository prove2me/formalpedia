-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_absolute_continuity
-- name    : AvramDividend.Classical.unbounded_tilted_scale_absolute_continuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T22:38:45.842882+00:00
-- url     : https://prove2.me/theorems/0883e459-3837-4637-80a5-754b764aebb6
-- title:
--   Absolute continuity of the Esscher-tilted q-scale function at the positive Esscher root, for unbounded variation
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Let phi > 0 be a root of the Laplace exponent, psi(phi) = q, and let V be the Esscher-tilted function V(x) = exp(-phi x) W(x). Then V is continuously differentiable on the positive half-line. This is the absolute-continuity statement that the Wiener-Hopf argument needs: the Stieltjes measure of V is then absolutely continuous with a density, so the fundamental theorem of calculus converts the cumulative of the excursion-height measure into the interval identity V(b) = V(a) exp(integral of the tail of the excursion-height measure from a to b). The hypothesis of unbounded variation is exactly what excludes the bounded-variation renewal-density case, so no standing assumption is required: the integrable first moment of the positive part is not available when the Levy measure has an infinite first moment near zero, and the infinite-small-jump case is one of the regimes this theorem must cover. The statement is the analytic core of the smoothness criterion for scale functions; once V is C1, the excursion-height measure is recovered as the tail of the logarithmic derivative.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, the smoothness criterion in section 3 and the Wiener-Hopf factorisation in section 2; Kuznetsov, Kyprianou, Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, Corollary 2.2 and the absolute continuity of the scale function in the infinite-variation case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_tilted_scale_absolute_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
