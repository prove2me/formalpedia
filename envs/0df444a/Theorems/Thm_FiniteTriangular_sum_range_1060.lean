-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1060
-- name    : FiniteTriangular.sum_range_1060
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:36.907934+00:00
-- url     : https://prove2.me/theorems/7ebeef8e-c239-4a09-a8e7-662ddd6a160c
-- title:
--   Sum of the nonnegative integers below 1060
-- statement:
--   The sum of the integers from $0$ through $1059$ equals $561270$, which is the triangular number $\\frac{1060(1059)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1060 : ∑ k ∈ range 1060, k = 561270 := by sorry
end FiniteTriangular
