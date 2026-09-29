-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1120
-- name    : FiniteTriangular.sum_range_1120
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:57.057118+00:00
-- url     : https://prove2.me/theorems/3d12417a-d138-4135-b058-afb1701fd70d
-- title:
--   Sum of the nonnegative integers below 1120
-- statement:
--   The sum of the integers from $0$ through $1119$ equals $626640$, which is the triangular number $\\frac{1120(1119)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1120 : ∑ k ∈ range 1120, k = 626640 := by sorry
end FiniteTriangular
