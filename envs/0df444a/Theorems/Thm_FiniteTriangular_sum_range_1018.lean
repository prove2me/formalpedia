-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1018
-- name    : FiniteTriangular.sum_range_1018
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:04.112001+00:00
-- url     : https://prove2.me/theorems/b159fd64-cc8a-4a41-b64f-160e2be7a0ee
-- title:
--   Sum of the nonnegative integers below 1018
-- statement:
--   The sum of the integers from $0$ through $1017$ equals $517653$, which is the triangular number $\\frac{1018(1017)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1018 : ∑ k ∈ range 1018, k = 517653 := by sorry
end FiniteTriangular
