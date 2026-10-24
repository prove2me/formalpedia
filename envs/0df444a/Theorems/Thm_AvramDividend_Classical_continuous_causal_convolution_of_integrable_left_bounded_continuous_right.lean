-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_causal_convolution_of_integrable_left_bounded_continuous_right
-- name    : AvramDividend.Classical.continuous_causal_convolution_of_integrable_left_bounded_continuous_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:34:29.542063+00:00
-- url     : https://prove2.me/theorems/8a0362a2-04d7-48cf-9c02-6a022e191c06
-- title:
--   Continuous convolution with integrable left and bounded continuous right real kernels
-- statement:
--   If a real kernel f is Lebesgue integrable and a real kernel g is continuous and globally bounded, the additive convolution x↦∫ f(y)g(x−y)dy is globally continuous. This supports the cut-off decomposition of causal renewal kernel products when the smooth bounded factor is on the right.
-- source:
--   Pinned Mathlib BddAbove.continuous_convolution_right_of_integrable, applied with the bilinear multiplication map.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set ContinuousLinearMap

namespace AvramDividend.Classical
theorem continuous_causal_convolution_of_integrable_left_bounded_continuous_right
    (f g : ℝ → ℝ) (hfi : Integrable f volume)
    (hgb : BddAbove (Set.range fun x : ℝ => ‖g x‖))
    (hgc : Continuous g) :
    Continuous (fun x : ℝ => ∫ y : ℝ, f y * g (x - y) ∂volume) := by sorry
end AvramDividend.Classical
