-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1101
-- name    : FiniteTriangular.sum_range_1101
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:35.042286+00:00
-- url     : https://prove2.me/theorems/2beb9bf4-cdc5-4d5e-a923-127449e9f514
-- title:
--   Sum of the nonnegative integers below 1101
-- statement:
--   The sum of the integers from $0$ through $1100$ equals $605550$, which is the triangular number $\\frac{1101(1100)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1101 : ∑ k ∈ range 1101, k = 605550 := by sorry
end FiniteTriangular
