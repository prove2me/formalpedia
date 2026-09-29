-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1004
-- name    : FiniteTriangular.sum_range_1004
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:40.406987+00:00
-- url     : https://prove2.me/theorems/8df24aa9-4591-49b0-8699-45dfe82ea0e7
-- title:
--   Sum of the nonnegative integers below 1004
-- statement:
--   The sum of the integers from $0$ through $1003$ equals $503506$, which is the triangular number $\\frac{1004(1003)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1004 : ∑ k ∈ range 1004, k = 503506 := by sorry
end FiniteTriangular
