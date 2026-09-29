-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1003
-- name    : FiniteTriangular.sum_range_1003
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:32.159974+00:00
-- url     : https://prove2.me/theorems/711f4958-c180-4a5f-b380-9d60f1465f03
-- title:
--   Sum of the nonnegative integers below 1003
-- statement:
--   The sum of the integers from $0$ through $1002$ equals $502503$, which is the triangular number $\\frac{1003(1002)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1003 : ∑ k ∈ range 1003, k = 502503 := by sorry
end FiniteTriangular
