-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1127
-- name    : FiniteTriangular.sum_range_1127
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:31.190152+00:00
-- url     : https://prove2.me/theorems/fac4c1c2-07ff-4fe4-8819-686dd9e6f997
-- title:
--   Sum of the nonnegative integers below 1127
-- statement:
--   The sum of the integers from $0$ through $1126$ equals $634501$, which is the triangular number $\\frac{1127(1126)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1127 : ∑ k ∈ range 1127, k = 634501 := by sorry
end FiniteTriangular
