-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
-- name    : AvramDividend.Classical.unbounded_scale_discount_convolution_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:43:02.041127+00:00
-- url     : https://prove2.me/theorems/362c2bfe-ee23-42fe-8c47-4a86e63d892e
-- title:
--   Causal convolution order under increasing scale-function discounts
-- statement:
--   For three ordered nonnegative discount rates, the convolution of the first two scale functions is bounded above by the convolution of the last two. This analytic comparison implies monotonicity of discount secant slopes and convexity of the scale function in its discount parameter.
-- source:
--   Continuous finite-interval convolution integrability, interval-integral monotonicity, and the Proved pointwise discount monotonicity of scale functions.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_convolution_order
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ q₃ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0 ≤ q₃) (hq12 : q₁ ≤ q₂) (hq23 : q₂ ≤ q₃)
    (W₁ W₂ W₃ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hW₃ : IsScaleFunction X q₃ W₃) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) ≤
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₃ (x - s) := by sorry
