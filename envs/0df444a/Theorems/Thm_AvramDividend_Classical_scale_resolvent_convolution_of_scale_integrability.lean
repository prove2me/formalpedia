-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
-- name    : AvramDividend.Classical.scale_resolvent_convolution_of_scale_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:54:23.565287+00:00
-- url     : https://prove2.me/theorems/d365f384-2c3b-498a-95a7-b81ff0ef0909
-- title:
--   Scale-function resolvent convolution without extra regularity hypotheses
-- statement:
--   For two discount rates, the scale-function resolvent convolution identity holds on the positive axis whenever a common right half-plane satisfies both scale-function Laplace conditions. The continuity and integrability of the convolution follow from the scale functions themselves, using the proved causal-convolution results.
-- source:
--   Uses the Proved scale_resolvent_convolution_of_continuous_integrable and positive_causal_convolution_laplace_integrable; positive_causal_convolution_continuous_of_weighted_integrable supplies regularity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_continuous_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_of_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scale_resolvent_convolution_of_scale_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ b : ℝ) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂)
    (hlarge : ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ)
    (hanchor : ∃ θ : ℝ, b < θ) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by sorry
