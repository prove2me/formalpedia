-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1088
-- name    : FiniteTriangular.sum_range_1088
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:19.279861+00:00
-- url     : https://prove2.me/theorems/b8d38461-6003-4649-be14-799e7ec1a5fd
-- title:
--   Sum of the nonnegative integers below 1088
-- statement:
--   The sum of the integers from $0$ through $1087$ equals $591328$, which is the triangular number $\\frac{1088(1087)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1088 : ∑ k ∈ range 1088, k = 591328 := by sorry
end FiniteTriangular
