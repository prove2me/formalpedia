-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1079
-- name    : FiniteTriangular.sum_range_1079
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:24.933755+00:00
-- url     : https://prove2.me/theorems/c53e5a38-d5c4-4980-b727-897d69141f87
-- title:
--   Sum of the nonnegative integers below 1079
-- statement:
--   The sum of the integers from $0$ through $1078$ equals $581581$, which is the triangular number $\\frac{1079(1078)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1079 : ∑ k ∈ range 1079, k = 581581 := by sorry
end FiniteTriangular
