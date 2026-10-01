-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_total_profit_sum_identity
-- name    : ChatterjeeSamuelson.UniformEfficiency.total_profit_sum_identity
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-01T10:36:09.577766+00:00
-- url     : https://prove2.me/theorems/41b130fc-5f24-4ada-bb0d-874857a89416
-- title:
--   Example 1(c)(iii) summation: ex ante profits add to (vbar/16)(1+k)(2-k)
-- statement:
--   The two ex ante profit formulas from Examples 1(c)(i),(ii) add to the total (vbar/16)(1+k)(2-k); a pure ring identity.

import Mathlib

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(c)(iii), summation part (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §3, p. 842 [PDF 8]: "The sum of the
parties' profits is π_s + π_b = (v̄/16)(1 + k)(2 − k)").

With π_s(k) = (v̄/48)(2 − k)²(1 + k) and π_b(k) = (v̄/48)(1 + k)²(2 − k)
(Examples 1(c)(i),(ii)), the sum collapses: (2 − k)²(1 + k) + (1 + k)²(2 − k) =
3(1 + k)(2 − k), so the sum is (v̄/16)(1 + k)(2 − k). -/
theorem total_profit_sum_identity (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hv : 0 < vbar) :
    vbar / 48 * (2 - k) ^ 2 * (1 + k) + vbar / 48 * (1 + k) ^ 2 * (2 - k) =
      vbar / 16 * (1 + k) * (2 - k) := by sorry

end ChatterjeeSamuelson.UniformEfficiency
