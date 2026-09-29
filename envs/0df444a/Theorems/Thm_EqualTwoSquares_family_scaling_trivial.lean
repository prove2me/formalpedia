-- Prove2me | Theorems.Thm_EqualTwoSquares_family_scaling_trivial
-- name    : EqualTwoSquares.family_scaling_trivial
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:25:29.664892+00:00
-- url     : https://prove2.me/theorems/cbdbc1e5-9183-4ef1-a136-de3e4be40792
-- title:
--   No member of the family is a nontrivial integer multiple of another
-- statement:
--   Let m, n and k be integers. If the quadruple (1, n^2 - n + 1, 2n - 1, n^2 - n - 1) equals k times the quadruple (1, m^2 - m + 1, 2m - 1, m^2 - m - 1), then n = m. In particular distinct members of the family are not related by scalar multiplication by a nontrivial integer.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 3: no member of the family is a nontrivial integer multiple of another. -/
theorem family_scaling_trivial {m n k : ℤ}
    (h : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      k • ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1)) :
    n = m := by sorry

end EqualTwoSquares
