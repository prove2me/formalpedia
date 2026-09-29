-- Prove2me | Theorems.Thm_Esgk_nonabsolute_factor_square_bound
-- name    : Esgk.nonabsolute_factor_square_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:50:43.234899+00:00
-- url     : https://prove2.me/theorems/350d259d-c833-4441-92d9-90973eb35e78
-- title:
--   Nonabsolute case gives a square deficiency bound
-- statement:
--   If $4N \le d^2$, $nd \le N 2s$ and $d \le 2s$ then $n \le s^2$. A B\u00e9zout bound on the nonabsolute factor forces a square-root lower bound.
-- source:
--   esgk-on3 lean/Esgk/AdditiveExcessArithmetic.lean (Esgk.nonabsolute_factor_square_bound)

import Mathlib

namespace Esgk

/-- Nonabsolute branch (§16.2, (16.3)): with `4N ≤ d^2` (Bézout),
coverage `n * d ≤ N * (2s)` and `d ≤ 2s` force `n ≤ s * s`. -/
theorem nonabsolute_factor_square_bound (n s N d : ℕ) (hd1 : 1 ≤ d) (h4N : 4 * N ≤ d ^ 2)
    (hcov : n * d ≤ N * (2 * s)) (hds : d ≤ 2 * s) : n ≤ s * s  := by sorry

end Esgk
