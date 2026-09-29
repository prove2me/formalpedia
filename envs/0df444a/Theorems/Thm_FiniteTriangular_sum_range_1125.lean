-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1125
-- name    : FiniteTriangular.sum_range_1125
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:34.019002+00:00
-- url     : https://prove2.me/theorems/5c9a1122-ca95-4aaa-a4ff-a9d7e50a1a82
-- title:
--   Sum of the nonnegative integers below 1125
-- statement:
--   The sum of the integers from $0$ through $1124$ equals $632250$, which is the triangular number $\\frac{1125(1124)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1125 : ∑ k ∈ range 1125, k = 632250 := by sorry
end FiniteTriangular
