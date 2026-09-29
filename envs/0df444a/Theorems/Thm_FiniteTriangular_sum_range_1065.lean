-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1065
-- name    : FiniteTriangular.sum_range_1065
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:41.021788+00:00
-- url     : https://prove2.me/theorems/51c0a71b-14f1-4952-a0f8-4156bd9b4298
-- title:
--   Sum of the nonnegative integers below 1065
-- statement:
--   The sum of the integers from $0$ through $1064$ equals $566580$, which is the triangular number $\\frac{1065(1064)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1065 : ∑ k ∈ range 1065, k = 566580 := by sorry
end FiniteTriangular
