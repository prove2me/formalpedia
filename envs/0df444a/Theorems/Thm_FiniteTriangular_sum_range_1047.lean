-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1047
-- name    : FiniteTriangular.sum_range_1047
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:08.552129+00:00
-- url     : https://prove2.me/theorems/4aecbbcc-c50b-4ec0-b10c-01887955f05a
-- title:
--   Sum of the nonnegative integers below 1047
-- statement:
--   The sum of the integers from $0$ through $1046$ equals $547581$, which is the triangular number $\\frac{1047(1046)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1047 : ∑ k ∈ range 1047, k = 547581 := by sorry
end FiniteTriangular
