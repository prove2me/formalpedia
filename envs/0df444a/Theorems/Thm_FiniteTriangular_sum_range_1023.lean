-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1023
-- name    : FiniteTriangular.sum_range_1023
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:05.273977+00:00
-- url     : https://prove2.me/theorems/1ec4f93b-c5a2-4f10-afbc-dd3436027aef
-- title:
--   Sum of the nonnegative integers below 1023
-- statement:
--   The sum of the integers from $0$ through $1022$ equals $522753$, which is the triangular number $\\frac{1023(1022)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1023 : ∑ k ∈ range 1023, k = 522753 := by sorry
end FiniteTriangular
