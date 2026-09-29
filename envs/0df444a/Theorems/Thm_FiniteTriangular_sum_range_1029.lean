-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1029
-- name    : FiniteTriangular.sum_range_1029
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:45.720994+00:00
-- url     : https://prove2.me/theorems/74a2f9e6-7984-4b3d-8afa-a0dd02c656cf
-- title:
--   Sum of the nonnegative integers below 1029
-- statement:
--   The sum of the integers from $0$ through $1028$ equals $528906$, which is the triangular number $\\frac{1029(1028)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1029 : ∑ k ∈ range 1029, k = 528906 := by sorry
end FiniteTriangular
