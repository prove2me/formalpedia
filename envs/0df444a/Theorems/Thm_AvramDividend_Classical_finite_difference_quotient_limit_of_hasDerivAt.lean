-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_difference_quotient_limit_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_difference_quotient_limit_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:24:12.041322+00:00
-- url     : https://prove2.me/theorems/68cd2b87-fd84-41f7-833d-50d4ee9ec25d
-- title:
--   One-sided finite-difference quotient limits from HasDerivAt with nonzero derivative
-- statement:
--   Let W : R -> R be differentiable at a with nonzero derivative. Then the two one-sided finite-difference quotients eps*W(a-eps)/(W(a)-W(a-eps)) and eps*W(a+eps)/(W(a+eps)-W(a)) both tend to W(a)/W'(a) as eps -> 0+. This is the pure-analysis bridge used in the sandwich passage for the reflected-barrier boundary value (Proposition 1 of Avram-Palmowski-Pistorius): once stopped-renewal lower/upper bounds squeeze the barrier value between these quotients, the limit identifies the scale ratio.
-- source:
--   Pure-analysis bridge for AvramDividend.Classical.barrierSupValue_eq_scale_ratio (a8d4c941) sandwich passage toward barrier_strategy_value (Proposition 1); extracted as an independently useful lemma with no stochastic premises

import Mathlib

open Filter Topology

namespace AvramDividend.Classical

theorem finite_difference_quotient_limit_of_hasDerivAt
    (W : ℝ → ℝ) (a : ℝ)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => ε * W (a - ε) / (W a - W (a - ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) ∧
    Filter.Tendsto (fun ε : ℝ => ε * W (a + ε) / (W (a + ε) - W a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a / deriv W a)) := by sorry

end AvramDividend.Classical
