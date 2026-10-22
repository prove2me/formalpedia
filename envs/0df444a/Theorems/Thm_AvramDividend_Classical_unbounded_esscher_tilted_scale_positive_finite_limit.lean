-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_positive_finite_limit
-- name    : AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T22:08:29.651218+00:00
-- url     : https://prove2.me/theorems/644a82be-2981-40ce-8a33-f9f02dc55b89
-- title:
--   Positive finite limit of the unbounded-variation Esscher-tilted scale function
-- statement:
--   For q>0 and a positive root φ of ψ(φ)=q, the Esscher-normalised unbounded-variation q-scale function V(x)=exp(-φx)W(x) has a strictly positive finite limit as x tends to infinity. The expected limit is 1/ψ'(φ), by the Esscher change of measure and the renewal theorem for spectrally negative Lévy processes drifting to infinity. This is a separate stochastic asymptotic input to the flat-tail result and will permit reuse of a proved elementary calculus theorem for the logarithmic derivative.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, Esscher transform and tilted scale-function asymptotic; compare the Proved bounded-variation counterpart AvramDividend.Classical.bv_ac_esscher_tilted_scale_positive_finite_limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by sorry
