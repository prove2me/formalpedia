-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_diff_comp_left_of_hasDerivAt
-- name    : AvramDividend.Classical.finite_diff_comp_left_of_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:48:40.234143+00:00
-- url     : https://prove2.me/theorems/525b2648-ae48-426a-8af5-f400182d634e
-- title:
--   Left-shift continuity composition for finite-difference bridge
-- statement:
--   For a differentiable real function at a, W(a-eps) tends to W(a) as eps approaches 0 from the right. This is the continuity-composition step of the finite-difference bridge for barrierSupValue_eq_scale_ratio (a8d4c941), isolated so the parent bridge can use it without repeating the eventually-within argument.
-- source:
--   Continuity-composition helper for a8d4c941 finite-difference bridge: isolates hD.continuousAt composed with epsmapsto a-eps landing in Iio, used by both lower and upper quotient proofs

import Mathlib

open Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem finite_diff_comp_left_of_hasDerivAt {W : ℝ → ℝ} {a : ℝ}
    (hD : HasDerivAt W (deriv W a) a) :
    Filter.Tendsto (fun ε : ℝ => W (a - ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W a)) := by sorry

end AvramDividend.Classical
