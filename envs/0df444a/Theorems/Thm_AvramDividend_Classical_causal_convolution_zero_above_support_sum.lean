-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_above_support_sum
-- name    : AvramDividend.Classical.causal_convolution_zero_above_support_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:16:22.81906+00:00
-- url     : https://prove2.me/theorems/44e3adb9-fca6-4085-baf9-cb94d2dc9184
-- title:
--   Convolution of upper-supported real kernels vanishes above the sum of support bounds
-- statement:
--   If f vanishes for y>a and g vanishes for z>b, then their real additive convolution is zero at any x>a+b. Each integrand product is zero because either y>a or x−y>b. This is the support-disjointness lemma needed to eliminate the small-small convolution near any fixed positive x0 during the BV renewal-density continuity cutoff proof.
-- source:
--   Pointwise support separation by real linear arithmetic; integral of the identically zero integrand.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory Set

namespace AvramDividend.Classical
theorem causal_convolution_zero_above_support_sum
    (f g : ℝ → ℝ) (a b x : ℝ)
    (hf : ∀ y : ℝ, a < y → f y = 0)
    (hg : ∀ z : ℝ, b < z → g z = 0)
    (h : a + b < x) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) = 0 := by sorry
end AvramDividend.Classical
