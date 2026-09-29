-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1075
-- name    : FiniteTriangular.sum_range_1075
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:24.137085+00:00
-- url     : https://prove2.me/theorems/71156a3b-1f5c-4a2e-8a7b-520eb2cc6421
-- title:
--   Sum of the nonnegative integers below 1075
-- statement:
--   The sum of the integers from $0$ through $1074$ equals $577275$, which is the triangular number $\\frac{1075(1074)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1075 : ∑ k ∈ range 1075, k = 577275 := by sorry
end FiniteTriangular
