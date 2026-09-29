-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1054
-- name    : FiniteTriangular.sum_range_1054
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:55.016323+00:00
-- url     : https://prove2.me/theorems/365d57a0-e4bb-48cc-85db-4ff579d013a3
-- title:
--   Sum of the nonnegative integers below 1054
-- statement:
--   The sum of the integers from $0$ through $1053$ equals $554931$, which is the triangular number $\\frac{1054(1053)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1054 : ∑ k ∈ range 1054, k = 554931 := by sorry
end FiniteTriangular
