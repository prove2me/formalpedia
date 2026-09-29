-- Prove2me | Theorems.Thm_EqualTwoSquares_family_patterns_infinite
-- name    : EqualTwoSquares.family_patterns_infinite
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:25:17.781991+00:00
-- url     : https://prove2.me/theorems/37d6fb5c-5f30-489d-beba-55bd2882fa15
-- title:
--   Infinitely many distinct patterns arise from the family
-- statement:
--   The set of integer quadruples of the form (1, n^2 - n + 1, 2n - 1, n^2 - n - 1), as n ranges over the integers, is infinite.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 3: the family produces infinitely many distinct quadruples. -/
theorem family_patterns_infinite :
    (Set.range (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1))).Infinite := by sorry

end EqualTwoSquares
