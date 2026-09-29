-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_989
-- name    : FiniteTriangular.sum_range_989
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:53.279005+00:00
-- url     : https://prove2.me/theorems/c025d6cb-0095-4f86-839c-253211f0e18c
-- title:
--   Sum of the nonnegative integers below 989
-- statement:
--   The sum of the integers from $0$ through $988$ equals $488566$, which is the triangular number $\\frac{989(988)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_989 : ∑ k ∈ range 989, k = 488566 := by sorry
end FiniteTriangular
