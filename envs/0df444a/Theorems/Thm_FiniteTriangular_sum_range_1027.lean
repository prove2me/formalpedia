-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1027
-- name    : FiniteTriangular.sum_range_1027
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:46.812654+00:00
-- url     : https://prove2.me/theorems/e5d4c108-01d4-42ac-a5c2-dd212ba3cd40
-- title:
--   Sum of the nonnegative integers below 1027
-- statement:
--   The sum of the integers from $0$ through $1026$ equals $526851$, which is the triangular number $\\frac{1027(1026)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1027 : ∑ k ∈ range 1027, k = 526851 := by sorry
end FiniteTriangular
