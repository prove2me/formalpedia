-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1014
-- name    : FiniteTriangular.sum_range_1014
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:21.600281+00:00
-- url     : https://prove2.me/theorems/76f08a81-b19f-4478-b62b-366e086ec449
-- title:
--   Sum of the nonnegative integers below 1014
-- statement:
--   The sum of the integers from $0$ through $1013$ equals $513591$, which is the triangular number $\\frac{1014(1013)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1014 : ∑ k ∈ range 1014, k = 513591 := by sorry
end FiniteTriangular
