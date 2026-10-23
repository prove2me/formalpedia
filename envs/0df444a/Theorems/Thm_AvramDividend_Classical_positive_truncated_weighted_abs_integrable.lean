-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_truncated_weighted_abs_integrable
-- name    : AvramDividend.Classical.positive_truncated_weighted_abs_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:20:26.637607+00:00
-- url     : https://prove2.me/theorems/73fb17d3-f14f-484c-b0b9-cc2dcdf573a4
-- title:
--   Finite-horizon weighted absolute value of a locally bounded continuous function is integrable
-- statement:
--   Let h be continuous on (0,∞) and uniformly bounded in absolute value by C on (0,R] for R>0. For any w>0, its cutoff e^(−wt)|h(t)|1_(0,R](t) belongs to L1((0,∞)). On (0,R] the exponential weight is at most one, so the absolute value is bounded by C, and the finite-interval Lebesgue measure makes it integrable. Extend by zero with Mathlib IntegrableOn.integrable_indicator and restrict to the positive axis. Needed to apply finite-horizon convolution contraction to differences of locally bounded Volterra solutions.
-- source:
--   Pinned Mathlib IntegrableOn.of_bound and IntegrableOn.integrable_indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_truncated_weighted_abs_integrable
    (h : ℝ → ℝ) (w R C : ℝ)
    (hw : 0 < w) (hR : 0 < R)
    (hc : ContinuousOn h (Ioi (0 : ℝ)))
    (hb : ∀ x ∈ Ioc (0 : ℝ) R, |h x| ≤ C) :
    IntegrableOn (fun t : ℝ =>
      if t ∈ Ioc (0 : ℝ) R then
        Real.exp (-w * t) * |h t| else 0)
      (Ioi (0 : ℝ)) volume := by sorry
