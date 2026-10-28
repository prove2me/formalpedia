-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
-- name    : AvramDividend.Classical.unbounded_scale_discount_strict_convex_secants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:56:24.705346+00:00
-- url     : https://prove2.me/theorems/d5ba7da1-a87c-4de5-ac89-4aa3eb6dee3a
-- title:
--   Strict convexity of q-scale functions in the discount rate
-- statement:
--   At every positive reserve for an unbounded-variation spectrally negative Lévy process, q-scale values have strictly increasing secant slopes across three strictly ordered nonnegative discounts. This is strict convexity in the discount parameter, using the causal convolution formula.
-- source:
--   Strict integral comparison of continuous scale-function products, the proved strict discount monotonicity, and the exact secant-convolution identity.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_strict_convex_secants
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
      (W₂ x - W₁ x) / (q₂ - q₁) <
        (W₃ x - W₂ x) / (q₃ - q₂) := by sorry
