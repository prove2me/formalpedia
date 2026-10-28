-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_chord
-- name    : AvramDividend.Classical.unbounded_scale_discount_strict_chord
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:05:17.47898+00:00
-- url     : https://prove2.me/theorems/298fcfba-3e38-417f-b306-41d1aa6e7c85
-- title:
--   Strict discount convexity as a weighted chord inequality
-- statement:
--   For three strictly ordered nonnegative discounts and positive initial reserve, the intermediate q-scale function lies strictly below the affine chord joining the endpoint scale values. The weighted algebraic formulation is directly usable in convex optimisation and sensitivity calculations.
-- source:
--   Algebraic reformulation of the Proved strict increase in adjacent q-discount secant slopes.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_strict_chord
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
      (q₃ - q₁) * W₂ x <
        (q₃ - q₂) * W₁ x + (q₂ - q₁) * W₃ x := by sorry
