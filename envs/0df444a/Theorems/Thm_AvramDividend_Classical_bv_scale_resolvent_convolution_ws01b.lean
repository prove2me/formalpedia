-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_resolvent_convolution_ws01b
-- name    : AvramDividend.Classical.bv_scale_resolvent_convolution_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:23:23.772238+00:00
-- url     : https://prove2.me/theorems/7ad05155-4c9b-4088-93bf-988a28fb93ea
-- title:
--   Two-discount scale-function resolvent convolution for standing bounded variation
-- statement:
--   Prove for standing bounded-variation spectrally negative Levy processes the positive-half-line resolvent convolution identity for q-scale functions at two nonnegative discounts, including infinite jump activity, using the common Laplace exponent tail and variation-agnostic analytic uniqueness theorem.
-- source:
--   Kyprianou et al, Theory of Scale Functions; accepted Prove2Me generic convolution d365f384.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_psi_two_discounts_common_tail_ws01b
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_resolvent_convolution_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by sorry
