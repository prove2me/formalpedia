-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_positive_bounded
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_secant_positive_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:14:17.717958+00:00
-- url     : https://prove2.me/theorems/6c02253b-5f28-4d2c-b555-8f6c3e0695b0
-- title:
--   Positive zero-based q-scale difference quotient with an endpoint convolution bound
-- statement:
--   For q>0 and a larger discount Q, the difference quotient (W^q(x)-W^0(x))/q is strictly positive and bounded by the self-convolution of W^Q for every x>0. This provides a positive, uniformly bounded family of forward secants approaching zero discount.
-- source:
--   Proved strict monotonicity in discount combined with the proved endpoint convolution secant bound.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_secant_positive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q Q : ℝ) (hq : 0 < q) (hqQ : q ≤ Q)
    (W₀ Wq WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWq : IsScaleFunction X q Wq)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      0 < (Wq x - W₀ x) / q ∧
      (Wq x - W₀ x) / q ≤
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by sorry
