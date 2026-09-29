-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1005
-- name    : FiniteTriangular.sum_range_1005
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:31.858805+00:00
-- url     : https://prove2.me/theorems/0a0e211e-1796-4c4a-87a5-80666a74fec3
-- title:
--   Sum of the nonnegative integers below 1005
-- statement:
--   The sum of the integers from $0$ through $1004$ equals $504510$, which is the triangular number $\\frac{1005(1004)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1005 : ∑ k ∈ range 1005, k = 504510 := by sorry
end FiniteTriangular
