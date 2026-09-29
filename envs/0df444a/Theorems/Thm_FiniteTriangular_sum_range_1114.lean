-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1114
-- name    : FiniteTriangular.sum_range_1114
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:56.059311+00:00
-- url     : https://prove2.me/theorems/b9311864-5b5d-4b7c-9576-3d587823287f
-- title:
--   Sum of the nonnegative integers below 1114
-- statement:
--   The sum of the integers from $0$ through $1113$ equals $619941$, which is the triangular number $\\frac{1114(1113)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1114 : ∑ k ∈ range 1114, k = 619941 := by sorry
end FiniteTriangular
