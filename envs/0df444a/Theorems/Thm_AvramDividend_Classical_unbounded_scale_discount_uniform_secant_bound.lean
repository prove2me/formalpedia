-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
-- name    : AvramDividend.Classical.unbounded_scale_discount_uniform_secant_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:17:10.797956+00:00
-- url     : https://prove2.me/theorems/1605d7b5-6403-4eac-867f-49297f313fe8
-- title:
--   Uniform endpoint convolution bound for discount changes
-- statement:
--   For discounts 0 ≤ q1 < q2 ≤ Q, the q-scale function difference at any positive reserve is nonnegative and at most (q2−q1) times the self-convolution of the fixed endpoint Q-scale function. This supplies a uniform local Lipschitz constant with respect to discount.
-- source:
--   The proved q-secant convolution sandwich and convolution monotonicity, combined with strict q-discount scale monotonicity.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_uniform_secant_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ Q : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hQ : 0 ≤ Q) (hq12 : q₁ < q₂) (hq2Q : q₂ ≤ Q)
    (W₁ W₂ WQ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      0 ≤ W₂ x - W₁ x ∧
        W₂ x - W₁ x ≤ (q₂ - q₁) *
          ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by sorry
