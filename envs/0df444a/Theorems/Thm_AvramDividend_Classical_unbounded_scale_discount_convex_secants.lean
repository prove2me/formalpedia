-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convex_secants
-- name    : AvramDividend.Classical.unbounded_scale_discount_convex_secants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:51:43.567614+00:00
-- url     : https://prove2.me/theorems/8d83c714-a70c-4067-87e5-7a2856fd7f74
-- title:
--   Convexity of unbounded-variation q-scale functions in discount
-- statement:
--   For strictly increasing nonnegative discount rates q1<q2<q3, the scale-function secant slope over [q1,q2] is at most the secant slope over [q2,q3] at any fixed positive reserve. This is the three-point criterion for convexity in the discount parameter.
-- source:
--   The proved exact secant-convolution identity and the ordered convolution comparison for three discounts.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_convex_secants
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ q₃ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0 ≤ q₃) (hq12 : q₁ < q₂) (hq23 : q₂ < q₃)
    (W₁ W₂ W₃ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hW₃ : IsScaleFunction X q₃ W₃) :
    ∀ x : ℝ, 0 < x →
      (W₂ x - W₁ x) / (q₂ - q₁) ≤
        (W₃ x - W₂ x) / (q₃ - q₂) := by sorry
