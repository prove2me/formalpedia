-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
-- name    : AvramDividend.Classical.avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:50:36.301489+00:00
-- url     : https://prove2.me/theorems/d3470902-4ff6-4c60-9bbf-d476fb6a5549
-- title:
--   Gaussian combined small-cell bound from source one-sided positive Taylor control, discount width and Hessian cross
-- statement:
--   The combined discounted Gaussian source cell positive residual is bounded using merely a bound on the positive part of the Taylor residual weighted at the cell start. This weaker and sufficient hypothesis matches the proved original Gaussian a194 source result; the other terms are controlled by the discount width and the raw-centred quadratic cross. Its companion a212 used a stronger absolute Taylor hypothesis that was not supplied by a194.
-- source:
--   Original stopped Gaussian a194 positive Taylor and a212 algebraic combined source; needed for actual a216 upper verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
    (e0 e1 u v d h r z ε Q L M : ℝ)
    (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
    (hε : 0 ≤ ε) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTaylor : max (e0 * (v - u - d*r - h/2*r^2)) 0 ≤ ε*r^2)
    (hDisc : |e1-e0| ≤ Q) (hLip : |v-u| ≤ L*|r|)
    (hh : |h| ≤ M) :
    max (e1 * (v-u) - e0 * (d*r + h/2*z^2)) 0 ≤
      ε*r^2 + Q*L*|r| + M/2*|r^2-z^2| := by sorry
