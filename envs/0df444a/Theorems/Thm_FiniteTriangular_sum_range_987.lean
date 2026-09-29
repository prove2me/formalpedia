-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_987
-- name    : FiniteTriangular.sum_range_987
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:58.038319+00:00
-- url     : https://prove2.me/theorems/04344b3a-b406-4f1b-91c5-97f48333aae1
-- title:
--   Sum of the nonnegative integers below 987
-- statement:
--   The sum of the integers from $0$ through $986$ equals $486591$, which is the triangular number $\\frac{987(986)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_987 : ∑ k ∈ range 987, k = 486591 := by sorry
end FiniteTriangular
