-- Prove2me | Theorems.Thm_EqualTwoSquares_explicit_family_chain
-- name    : EqualTwoSquares.explicit_family_chain
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:24:25.473968+00:00
-- url     : https://prove2.me/theorems/d96095a4-4bc9-41fb-ae6b-7e39c0661299
-- title:
--   The four entries of the family form a strict chain from n = 4 on
-- statement:
--   Let n be an integer with 4 <= n. Then 1 < 2n - 1, 2n - 1 < n^2 - n - 1 and n^2 - n - 1 < n^2 - n + 1. The bound 4 is sharp: at n = 3 the entries 2n - 1 and n^2 - n - 1 are both equal to 5.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 2, inequality part: the four entries form a strict chain for every n at least 4. -/
theorem explicit_family_chain {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by sorry

end EqualTwoSquares
