-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1078
-- name    : FiniteTriangular.sum_range_1078
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:24.2188+00:00
-- url     : https://prove2.me/theorems/6ff0d7b1-8188-4f59-bf2d-64c0a396185c
-- title:
--   Sum of the nonnegative integers below 1078
-- statement:
--   The sum of the integers from $0$ through $1077$ equals $580503$, which is the triangular number $\\frac{1078(1077)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1078 : ∑ k ∈ range 1078, k = 580503 := by sorry
end FiniteTriangular
