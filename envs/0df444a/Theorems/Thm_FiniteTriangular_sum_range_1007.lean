-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1007
-- name    : FiniteTriangular.sum_range_1007
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:43.037+00:00
-- url     : https://prove2.me/theorems/98f743f9-c4f1-4e0a-8cac-7880ab23190c
-- title:
--   Sum of the nonnegative integers below 1007
-- statement:
--   The sum of the integers from $0$ through $1006$ equals $506521$, which is the triangular number $\\frac{1007(1006)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1007 : ∑ k ∈ range 1007, k = 506521 := by sorry
end FiniteTriangular
