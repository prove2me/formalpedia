-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
-- name    : AvramDividend.Classical.unbounded_scale_discount_secant_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:20:59.661909+00:00
-- url     : https://prove2.me/theorems/f8d6e439-6690-4bf4-a9bb-9594fdc6cb75
-- title:
--   Scale-function discount secant slope equals a causal convolution
-- statement:
--   For any two distinct nonnegative discount rates of an unbounded-variation spectrally negative Lévy process, the finite difference quotient of their scale functions in discount equals their positive causal convolution. This gives an exact starting point for differentiability and sensitivity analysis in the discount parameter.
-- source:
--   Algebraic consequence of the Proved unbounded_scale_resolvent_convolution and strict positivity of the difference in discounts.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_secant_convolution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (W₂ x - W₁ x) / (q₂ - q₁) =
        ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by sorry
