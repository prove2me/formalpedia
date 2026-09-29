-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1066
-- name    : FiniteTriangular.sum_range_1066
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:40.152436+00:00
-- url     : https://prove2.me/theorems/6646c949-2563-4387-a8b8-c6e08fdad4e6
-- title:
--   Sum of the nonnegative integers below 1066
-- statement:
--   The sum of the integers from $0$ through $1065$ equals $567645$, which is the triangular number $\\frac{1066(1065)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1066 : ∑ k ∈ range 1066, k = 567645 := by sorry
end FiniteTriangular
