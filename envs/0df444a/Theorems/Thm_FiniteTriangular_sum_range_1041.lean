-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1041
-- name    : FiniteTriangular.sum_range_1041
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:08.796515+00:00
-- url     : https://prove2.me/theorems/2ea4adee-57ff-43ce-b32a-8082c4b837e5
-- title:
--   Sum of the nonnegative integers below 1041
-- statement:
--   The sum of the integers from $0$ through $1040$ equals $541320$, which is the triangular number $\\frac{1041(1040)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1041 : ∑ k ∈ range 1041, k = 541320 := by sorry
end FiniteTriangular
