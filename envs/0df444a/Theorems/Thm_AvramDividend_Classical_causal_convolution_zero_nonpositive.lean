-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_zero_nonpositive
-- name    : AvramDividend.Classical.causal_convolution_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:07:54.183993+00:00
-- url     : https://prove2.me/theorems/1a6f4c0f-1362-4554-a810-922ae085c5c1
-- title:
--   The additive convolution of causal kernels vanishes on nonpositive times
-- statement:
--   If real kernels f and g vanish on (-∞,0], then their Lebesgue convolution ∫ f(y)g(x−y)dy vanishes at every x≤0. This propagates one-sided support through the BV Esscher renewal-density convolution recursion and requires no integrability assumption because the integrand is identically zero.
-- source:
--   Pointwise support argument for causal convolution; the integrand vanishes because y and x−y cannot both be positive when x≤0.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory Set

namespace AvramDividend.Classical
theorem causal_convolution_zero_nonpositive
    (f g : ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hgzero : ∀ x : ℝ, x ≤ 0 → g x = 0)
    (x : ℝ) (hx : x ≤ 0) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) = 0 := by sorry
end AvramDividend.Classical
