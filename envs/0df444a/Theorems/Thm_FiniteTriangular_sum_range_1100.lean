-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1100
-- name    : FiniteTriangular.sum_range_1100
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:36.122838+00:00
-- url     : https://prove2.me/theorems/3a58b100-d03c-4b71-8c5c-47f5bebb2f07
-- title:
--   Sum of the nonnegative integers below 1100
-- statement:
--   The sum of the integers from $0$ through $1099$ equals $604450$, which is the triangular number $\\frac{1100(1099)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1100 : ∑ k ∈ range 1100, k = 604450 := by sorry
end FiniteTriangular
