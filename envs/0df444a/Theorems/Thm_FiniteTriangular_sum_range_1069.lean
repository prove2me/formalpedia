-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1069
-- name    : FiniteTriangular.sum_range_1069
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:41.705503+00:00
-- url     : https://prove2.me/theorems/1b9fee6d-f431-4bf6-9c9f-29e55bf6dead
-- title:
--   Sum of the nonnegative integers below 1069
-- statement:
--   The sum of the integers from $0$ through $1068$ equals $570846$, which is the triangular number $\\frac{1069(1068)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1069 : ∑ k ∈ range 1069, k = 570846 := by sorry
end FiniteTriangular
