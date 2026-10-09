-- Prove2me | Theorems.Thm_AvramDividend_Classical_origin_crossing_compensated_increment_linear_bound
-- name    : AvramDividend.Classical.origin_crossing_compensated_increment_linear_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:26:41.789555+00:00
-- url     : https://prove2.me/theorems/e1b2764c-23fe-40a8-b73f-9f651bed61d2
-- title:
--   Linear bound for the compensated scale-function increment on an origin-crossing jump
-- statement:
--   For x>0,y<0 with x+y≤0, assume W=0 on the nonpositive half-line and |W(x)|≤Kx, |W'(x)|≤K. Then the compensated increment |W(x+y)-W(x)-yW'(x)| is at most 2K|y|. Since the crossing-state strip has width |y|, the resulting state-integrated error is quadratic in the jump size. This lemma supplies the pointwise bound needed by the boundary-layer Fubini argument without falsely asserting per-jump quadratic domination.
-- source:
--   Elementary origin-crossing scale-function estimate as a component of the Avram Dividend q-harmonic generator proof.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem origin_crossing_compensated_increment_linear_bound
    (W : ℝ → ℝ) (x y K : ℝ)
    (hx : 0 < x) (hy : y < 0) (hcross : x + y ≤ 0)
    (hK : 0 ≤ K)
    (hWneg : ∀ z : ℝ, z ≤ 0 → W z = 0)
    (hWval : |W x| ≤ K * x)
    (hD : |deriv W x| ≤ K) :
    |W (x + y) - W x - deriv W x * y| ≤ 2 * K * (-y) := by sorry

end AvramDividend.Classical
