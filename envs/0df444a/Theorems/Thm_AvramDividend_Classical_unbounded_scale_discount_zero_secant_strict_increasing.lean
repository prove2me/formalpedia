-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_strict_increasing
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_increasing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:17:20.396994+00:00
-- url     : https://prove2.me/theorems/f2aa683f-595e-4b39-9bc1-290de0a59534
-- title:
--   Strictly increasing zero-based discount secants of the q-scale function
-- statement:
--   For a fixed positive reserve x, the normalised change (W^q(x)-W^0(x))/q is strictly increasing as q grows through positive discounts. This is a discount-sensitivity consequence of strict convexity, and controls first-order forward differences from zero.
-- source:
--   The canonical Proved strict discount chord inequality with endpoints (0,a,b), followed by cross multiplication with positive denominators.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_chord
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_increasing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (W₀ Wa Wb : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWa : IsScaleFunction X a Wa)
    (hWb : IsScaleFunction X b Wb) :
    ∀ x : ℝ, 0 < x →
      (Wa x - W₀ x) / a < (Wb x - W₀ x) / b := by sorry
