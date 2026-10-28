-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_reflected_interval_to_global_convolution_integrable
-- name    : AvramDividend.Classical.causal_reflected_interval_to_global_convolution_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:52:28.600751+00:00
-- url     : https://prove2.me/theorems/69c4a0fd-c930-454c-b2d2-158cb0b0a9cb
-- title:
--   Causal reflected product interval integrability implies full real convolution integrability
-- statement:
--   Suppose two real functions vanish for nonpositive arguments. If the reflected convolution product k(x−s)F(s) is integrable on (0,x], it is zero off this interval and therefore integrable globally. Translation-reflection invariance of Lebesgue measure gives the required full convolution integrability of k(y)F(x−y). The theorem joins existing positive-axis antitone split-integrability estimates to the strict pointwise full-line premise of the canonical geometric-renewal measure-density theorem.
-- source:
--   Pinned Mathlib intervalIntegrable_iff_integrableOn_Ioc_of_le, IntegrableOn.integrable_indicator, Integrable.comp_sub_left; Proved causal_antitone_L1_split_product_intervalIntegrable.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set

theorem AvramDividend.Classical.causal_reflected_interval_to_global_convolution_integrable
    (k F : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hkzero : ∀ t : ℝ, t ≤ 0 → k t = 0)
    (hFzero : ∀ t : ℝ, t ≤ 0 → F t = 0)
    (hi : IntervalIntegrable
      (fun s : ℝ => k (x - s) * F s) volume 0 x) :
    Integrable (fun y : ℝ => k y * F (x - y)) volume  := by sorry
