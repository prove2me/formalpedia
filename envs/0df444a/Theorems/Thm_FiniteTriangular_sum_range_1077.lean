-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1077
-- name    : FiniteTriangular.sum_range_1077
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:20.741287+00:00
-- url     : https://prove2.me/theorems/be0afa0d-cbdd-40c5-898e-fa7b7995a9d3
-- title:
--   Sum of the nonnegative integers below 1077
-- statement:
--   The sum of the integers from $0$ through $1076$ equals $579426$, which is the triangular number $\\frac{1077(1076)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1077 : ∑ k ∈ range 1077, k = 579426 := by sorry
end FiniteTriangular
