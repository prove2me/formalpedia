-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1055
-- name    : FiniteTriangular.sum_range_1055
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:55.009805+00:00
-- url     : https://prove2.me/theorems/bad3497b-5e47-47f9-a99d-649d4d4b1918
-- title:
--   Sum of the nonnegative integers below 1055
-- statement:
--   The sum of the integers from $0$ through $1054$ equals $555985$, which is the triangular number $\\frac{1055(1054)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1055 : ∑ k ∈ range 1055, k = 555985 := by sorry
end FiniteTriangular
