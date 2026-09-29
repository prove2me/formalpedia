-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1123
-- name    : FiniteTriangular.sum_range_1123
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:34.234198+00:00
-- url     : https://prove2.me/theorems/0845b2d3-bcd9-47c2-ab2e-6706cea447b4
-- title:
--   Sum of the nonnegative integers below 1123
-- statement:
--   The sum of the integers from $0$ through $1122$ equals $630003$, which is the triangular number $\\frac{1123(1122)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1123 : ∑ k ∈ range 1123, k = 630003 := by sorry
end FiniteTriangular
