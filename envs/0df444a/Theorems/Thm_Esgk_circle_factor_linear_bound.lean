-- Prove2me | Theorems.Thm_Esgk_circle_factor_linear_bound
-- name    : Esgk.circle_factor_linear_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:49:21.207845+00:00
-- url     : https://prove2.me/theorems/bd66cc66-afaf-4164-af99-262ef5659570
-- title:
--   Circle case gives a linear deficiency bound
-- statement:
--   If $N \le 3$ and $2n \le N 2s$ then $n \le 3s$. A degree-2 carrier factor holds few points, so the deficiency is linear in this branch.
-- source:
--   esgk-on3 lean/Esgk/AdditiveExcessArithmetic.lean (Esgk.circle_factor_linear_bound)

import Mathlib

namespace Esgk

/-- Circle branch (§16.1, (16.1)): a degree-2 factor carries at most 3
points, so `n * 2 ≤ N * (2s)` with `N ≤ 3` forces `n ≤ 3s`. -/
theorem circle_factor_linear_bound (n s N : ℕ) (hN3 : N ≤ 3)
    (hcov : n * 2 ≤ N * (2 * s)) : n ≤ 3 * s  := by sorry

end Esgk
