-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1098
-- name    : FiniteTriangular.sum_range_1098
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:33.418674+00:00
-- url     : https://prove2.me/theorems/f026e112-c668-4d59-9a7a-7a0d007de55e
-- title:
--   Sum of the nonnegative integers below 1098
-- statement:
--   The sum of the integers from $0$ through $1097$ equals $602253$, which is the triangular number $\\frac{1098(1097)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1098 : ∑ k ∈ range 1098, k = 602253 := by sorry
end FiniteTriangular
