-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1115
-- name    : FiniteTriangular.sum_range_1115
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:58.712615+00:00
-- url     : https://prove2.me/theorems/235811c3-46ce-41e4-998b-4292e8b3a85d
-- title:
--   Sum of the nonnegative integers below 1115
-- statement:
--   The sum of the integers from $0$ through $1114$ equals $621055$, which is the triangular number $\\frac{1115(1114)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1115 : ∑ k ∈ range 1115, k = 621055 := by sorry
end FiniteTriangular
