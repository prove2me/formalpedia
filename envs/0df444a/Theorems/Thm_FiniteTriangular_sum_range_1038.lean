-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1038
-- name    : FiniteTriangular.sum_range_1038
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:43.139983+00:00
-- url     : https://prove2.me/theorems/8949e84e-27df-4916-a2b1-e20414b6a0f3
-- title:
--   Sum of the nonnegative integers below 1038
-- statement:
--   The sum of the integers from $0$ through $1037$ equals $538203$, which is the triangular number $\\frac{1038(1037)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1038 : ∑ k ∈ range 1038, k = 538203 := by sorry
end FiniteTriangular
