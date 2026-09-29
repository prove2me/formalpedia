-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1093
-- name    : FiniteTriangular.sum_range_1093
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:51.370683+00:00
-- url     : https://prove2.me/theorems/2e6d2d26-fab4-4a46-8eb3-05390276fced
-- title:
--   Sum of the nonnegative integers below 1093
-- statement:
--   The sum of the integers from $0$ through $1092$ equals $596778$, which is the triangular number $\\frac{1093(1092)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1093 : ∑ k ∈ range 1093, k = 596778 := by sorry
end FiniteTriangular
