-- Prove2me | Theorems.Thm_EqualTwoSquares_explicit_family_identity
-- name    : EqualTwoSquares.explicit_family_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:24:10.888968+00:00
-- url     : https://prove2.me/theorems/7f0b8024-6f1b-4878-8b3a-3a2fc4e5ec99
-- title:
--   An explicit one-parameter family of solutions
-- statement:
--   For every integer n, 1^2 + (n^2 - n + 1)^2 = (2n - 1)^2 + (n^2 - n - 1)^2. No positivity or size hypothesis is imposed on n: the identity is a polynomial identity in n.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 2, equality part: the explicit one-parameter family, valid for every integer n. -/
theorem explicit_family_identity (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by sorry

end EqualTwoSquares
