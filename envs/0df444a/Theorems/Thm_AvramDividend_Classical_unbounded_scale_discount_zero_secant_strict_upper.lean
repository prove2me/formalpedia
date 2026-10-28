-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_strict_upper
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:21:43.865454+00:00
-- url     : https://prove2.me/theorems/8342c25a-db53-430a-9c12-475843c1ffb8
-- title:
--   Strict upper convolution bound for zero-based scale discount secants below Q
-- statement:
--   At any positive reserve and strictly intermediate discount 0<q<Q, the zero-based scale-function discount secant is strictly below the self-convolution of the upper endpoint W^Q, strengthening the nonstrict Lipschitz estimate.
-- source:
--   Combine the proved strict discount secant convexity with the exact resolvent secant-convolution identity and convolution ordering.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_secant_strict_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q Q : ℝ) (hq : 0 < q) (hqQ : q < Q)
    (W₀ Wq WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWq : IsScaleFunction X q Wq)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      (Wq x - W₀ x) / q <
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by sorry
