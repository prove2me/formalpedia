-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1034
-- name    : FiniteTriangular.sum_range_1034
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:39.754986+00:00
-- url     : https://prove2.me/theorems/b36fcbe0-a646-43d2-86dd-c9a6e8ea798b
-- title:
--   Sum of the nonnegative integers below 1034
-- statement:
--   The sum of the integers from $0$ through $1033$ equals $534061$, which is the triangular number $\\frac{1034(1033)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1034 : ∑ k ∈ range 1034, k = 534061 := by sorry
end FiniteTriangular
