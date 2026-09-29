-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1068
-- name    : FiniteTriangular.sum_range_1068
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:37.952805+00:00
-- url     : https://prove2.me/theorems/2593da2b-9ea4-4384-abe3-47ae25f54883
-- title:
--   Sum of the nonnegative integers below 1068
-- statement:
--   The sum of the integers from $0$ through $1067$ equals $569778$, which is the triangular number $\\frac{1068(1067)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1068 : ∑ k ∈ range 1068, k = 569778 := by sorry
end FiniteTriangular
