-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1119
-- name    : FiniteTriangular.sum_range_1119
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:55.879411+00:00
-- url     : https://prove2.me/theorems/553d94d4-1d2a-4d8d-aaaf-7ae5c7f943c0
-- title:
--   Sum of the nonnegative integers below 1119
-- statement:
--   The sum of the integers from $0$ through $1118$ equals $625521$, which is the triangular number $\\frac{1119(1118)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1119 : ∑ k ∈ range 1119, k = 625521 := by sorry
end FiniteTriangular
