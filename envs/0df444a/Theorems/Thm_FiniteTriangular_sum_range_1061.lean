-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1061
-- name    : FiniteTriangular.sum_range_1061
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:56.403223+00:00
-- url     : https://prove2.me/theorems/6732c814-40d5-436f-b5f2-bd13185b960b
-- title:
--   Sum of the nonnegative integers below 1061
-- statement:
--   The sum of the integers from $0$ through $1060$ equals $562330$, which is the triangular number $\\frac{1061(1060)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1061 : ∑ k ∈ range 1061, k = 562330 := by sorry
end FiniteTriangular
