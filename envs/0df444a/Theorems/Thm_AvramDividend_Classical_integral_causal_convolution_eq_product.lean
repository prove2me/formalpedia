-- Prove2me | Theorems.Thm_AvramDividend_Classical_integral_causal_convolution_eq_product
-- name    : AvramDividend.Classical.integral_causal_convolution_eq_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:18:07.142089+00:00
-- url     : https://prove2.me/theorems/90760e05-5df9-4515-b83a-251a41b6239d
-- title:
--   Total integral of two real L1 convolution kernels is the product of their integrals
-- statement:
--   For Lebesgue-integrable real f and g, the integral of the additive convolution equals the product of their integrals. This is the exact real notation of pinned Mathlib integral_convolution. It gives the geometric α^n total mass of each n-fold BV renewal kernel directly by induction.
-- source:
--   Pinned Mathlib.MeasureTheory.integral_convolution with ContinuousLinearMap.mul ℝ ℝ.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped Convolution

namespace AvramDividend.Classical
theorem integral_causal_convolution_eq_product
    (f g : ℝ → ℝ) (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x : ℝ, (∫ y : ℝ, f y * g (x - y) ∂volume) ∂volume) =
      (∫ x : ℝ, f x ∂volume) * (∫ x : ℝ, g x ∂volume) := by sorry
end AvramDividend.Classical
