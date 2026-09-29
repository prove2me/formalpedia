-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1103
-- name    : FiniteTriangular.sum_range_1103
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:36.944987+00:00
-- url     : https://prove2.me/theorems/c053967e-f08e-453b-a139-c30492870bbe
-- title:
--   Sum of the nonnegative integers below 1103
-- statement:
--   The sum of the integers from $0$ through $1102$ equals $607753$, which is the triangular number $\\frac{1103(1102)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1103 : ∑ k ∈ range 1103, k = 607753 := by sorry
end FiniteTriangular
