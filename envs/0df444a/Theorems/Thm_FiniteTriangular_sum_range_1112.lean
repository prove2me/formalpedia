-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1112
-- name    : FiniteTriangular.sum_range_1112
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:26.946682+00:00
-- url     : https://prove2.me/theorems/2db38042-4381-4836-8acd-5ae4c3653381
-- title:
--   Sum of the nonnegative integers below 1112
-- statement:
--   The sum of the integers from $0$ through $1111$ equals $617716$, which is the triangular number $\\frac{1112(1111)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1112 : ∑ k ∈ range 1112, k = 617716 := by sorry
end FiniteTriangular
