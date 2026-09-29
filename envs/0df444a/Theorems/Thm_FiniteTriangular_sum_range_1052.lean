-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1052
-- name    : FiniteTriangular.sum_range_1052
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:54.109485+00:00
-- url     : https://prove2.me/theorems/f58feee0-c834-43f9-9722-3e9e8e8cd1aa
-- title:
--   Sum of the nonnegative integers below 1052
-- statement:
--   The sum of the integers from $0$ through $1051$ equals $552826$, which is the triangular number $\\frac{1052(1051)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1052 : ∑ k ∈ range 1052, k = 552826 := by sorry
end FiniteTriangular
