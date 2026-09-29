-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1012
-- name    : FiniteTriangular.sum_range_1012
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:16.798331+00:00
-- url     : https://prove2.me/theorems/ee23fcd3-1637-4383-b154-569ca5d10a88
-- title:
--   Sum of the nonnegative integers below 1012
-- statement:
--   The sum of the integers from $0$ through $1011$ equals $511566$, which is the triangular number $\\frac{1012(1011)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1012 : ∑ k ∈ range 1012, k = 511566 := by sorry
end FiniteTriangular
