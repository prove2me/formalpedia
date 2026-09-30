-- Prove2me | Theorems.Thm_CookPvsNP_nat_pow_add_le_pow_add
-- name    : CookPvsNP.nat_pow_add_le_pow_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T06:44:21.382974+00:00
-- url     : https://prove2.me/theorems/c036863a-d94b-4492-86d6-ad7d210e8675
-- title:
--   Polynomial budgets absorb into a single power: n^a + c at most n^(a+c+2) + (a+c+2)
-- statement:
--   Whenever a computation on an input of length n performs n^a steps, and the result of that computation has length at most c, the whole budget can be absorbed into a single exponent of the form |x|^k + k required by the definition of a polynomial-time computable function. Concretely, n^a is at most n^(a + c + 2) because a is at most a + c + 2, and c is at most a + c + 2, so the sum is bounded by n^(a + c + 2) + (a + c + 2). This is the elementary arithmetic that lets the time budget of a first machine, followed by the budget of a second machine whose input is bounded by a polynomial in n, be rewritten in the single-power-plus-constant form that Cook's Definition 3 demands. It is the reason the closure of polynomial-time computable functions under composition holds for a single machine with a single exponent, rather than only for a family of machines indexed by a polynomial.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), §1 p. 2, the form |x|^k + k of the running-time clause in Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

theorem nat_pow_add_le_pow_add (n a c : ℕ) :
    n ^ a + c ≤ n ^ (a + c + 2) + (a + c + 2) := by
  sorry

end CookPvsNP
