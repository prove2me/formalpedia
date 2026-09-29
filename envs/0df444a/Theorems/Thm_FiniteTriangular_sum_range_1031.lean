-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1031
-- name    : FiniteTriangular.sum_range_1031
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:50.747988+00:00
-- url     : https://prove2.me/theorems/470b0431-3558-42d3-8532-e64221c9e9f6
-- title:
--   Sum of the nonnegative integers below 1031
-- statement:
--   The sum of the integers from $0$ through $1030$ equals $530965$, which is the triangular number $\\frac{1031(1030)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1031 : ∑ k ∈ range 1031, k = 530965 := by sorry
end FiniteTriangular
