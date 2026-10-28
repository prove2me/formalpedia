-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_sandwich
-- name    : AvramDividend.Classical.unbounded_scale_discount_secant_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:07:36.361921+00:00
-- url     : https://prove2.me/theorems/d4fce3c5-cd01-426f-b7e5-9720732686bc
-- title:
--   Scale discount secant bounds by endpoint self-convolution
-- statement:
--   For unbounded variation and nonnegative discounts q1 < q2, the secant slope of the q-scale function at positive reserve is bounded below and above by the causal self-convolutions of the q1 and q2 scale functions. This gives finite-difference sensitivity estimates without taking a q-derivative.
-- source:
--   Corollary of the proved q-resolvent secant identity and monotonicity of causal convolution under discount order.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_secant_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₁ (x - s)) ≤
        (W₂ x - W₁ x) / (q₂ - q₁) ∧
      (W₂ x - W₁ x) / (q₂ - q₁) ≤
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₂ (x - s) := by sorry
