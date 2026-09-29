-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1043
-- name    : FiniteTriangular.sum_range_1043
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:12.604296+00:00
-- url     : https://prove2.me/theorems/2a4206a8-6c8a-4b21-9767-23ea99129388
-- title:
--   Sum of the nonnegative integers below 1043
-- statement:
--   The sum of the integers from $0$ through $1042$ equals $543403$, which is the triangular number $\\frac{1043(1042)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1043 : ∑ k ∈ range 1043, k = 543403 := by sorry
end FiniteTriangular
