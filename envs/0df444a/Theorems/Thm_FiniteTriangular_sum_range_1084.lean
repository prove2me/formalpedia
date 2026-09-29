-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1084
-- name    : FiniteTriangular.sum_range_1084
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:16.170474+00:00
-- url     : https://prove2.me/theorems/9ac5feea-57a8-4cf8-8194-52dbcaf7b049
-- title:
--   Sum of the nonnegative integers below 1084
-- statement:
--   The sum of the integers from $0$ through $1083$ equals $586986$, which is the triangular number $\\frac{1084(1083)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1084 : ∑ k ∈ range 1084, k = 586986 := by sorry
end FiniteTriangular
