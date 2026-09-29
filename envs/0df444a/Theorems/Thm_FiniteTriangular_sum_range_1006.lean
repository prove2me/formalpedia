-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1006
-- name    : FiniteTriangular.sum_range_1006
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:42.232529+00:00
-- url     : https://prove2.me/theorems/227a1411-2faa-4033-bee4-9505e0c3429a
-- title:
--   Sum of the nonnegative integers below 1006
-- statement:
--   The sum of the integers from $0$ through $1005$ equals $505515$, which is the triangular number $\\frac{1006(1005)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1006 : ∑ k ∈ range 1006, k = 505515 := by sorry
end FiniteTriangular
