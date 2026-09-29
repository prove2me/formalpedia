-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1124
-- name    : FiniteTriangular.sum_range_1124
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:33.307405+00:00
-- url     : https://prove2.me/theorems/71e25407-81ac-40a2-ad53-149e1b64860b
-- title:
--   Sum of the nonnegative integers below 1124
-- statement:
--   The sum of the integers from $0$ through $1123$ equals $631126$, which is the triangular number $\\frac{1124(1123)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1124 : ∑ k ∈ range 1124, k = 631126 := by sorry
end FiniteTriangular
