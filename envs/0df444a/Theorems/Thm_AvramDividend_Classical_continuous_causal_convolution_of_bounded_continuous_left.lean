-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_causal_convolution_of_bounded_continuous_left
-- name    : AvramDividend.Classical.continuous_causal_convolution_of_bounded_continuous_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:14:06.84678+00:00
-- url     : https://prove2.me/theorems/50360dd3-a09e-4854-8ddd-8034075756da
-- title:
--   Convolution of a bounded continuous real function with an L1 kernel is continuous
-- statement:
--   The real additive convolution ∫f(y)g(x−y)dy is continuous if f is globally continuous and bounded and g is integrable. It wraps the pinned Mathlib BddAbove.continuous_convolution_left_of_integrable in the integral notation used by the BV Esscher renewal-density proof. It is the regular component after truncating an integrable causal kernel away from zero.
-- source:
--   Mathlib Analysis.Convolution, BddAbove.continuous_convolution_left_of_integrable, instantiated with mul ℝ ℝ and real Lebesgue volume.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped Convolution

namespace AvramDividend.Classical
theorem continuous_causal_convolution_of_bounded_continuous_left
    (f g : ℝ → ℝ) (hfc : Continuous f)
    (hfb : BddAbove (Set.range fun x : ℝ => ‖f x‖))
    (hgi : Integrable g volume) :
    Continuous (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) := by sorry
end AvramDividend.Classical
