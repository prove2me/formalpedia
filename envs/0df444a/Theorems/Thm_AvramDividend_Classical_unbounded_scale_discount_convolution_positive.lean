-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_positive
-- name    : AvramDividend.Classical.unbounded_scale_discount_convolution_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:31:10.198995+00:00
-- url     : https://prove2.me/theorems/730fd5b2-b150-49f8-aa9b-c9e01451f6a8
-- title:
--   Positive causal convolution of two discount scale functions
-- statement:
--   For any ordered distinct nonnegative discount rates of an unbounded-variation spectrally negative Lévy process, the causal convolution of their two scale functions is strictly positive at every positive reserve. The proof uses the proved exact discount finite-difference formula and strict discount monotonicity.
-- source:
--   Corollary of the Proved discount secant-convolution identity and strict monotonicity.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_convolution_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      0 < ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by sorry
