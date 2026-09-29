-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1117
-- name    : FiniteTriangular.sum_range_1117
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:59.2612+00:00
-- url     : https://prove2.me/theorems/db768681-662b-4935-b487-5cc4cdb4bbb3
-- title:
--   Sum of the nonnegative integers below 1117
-- statement:
--   The sum of the integers from $0$ through $1116$ equals $623286$, which is the triangular number $\\frac{1117(1116)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1117 : ∑ k ∈ range 1117, k = 623286 := by sorry
end FiniteTriangular
