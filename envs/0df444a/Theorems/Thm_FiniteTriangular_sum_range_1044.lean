-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1044
-- name    : FiniteTriangular.sum_range_1044
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:12.941252+00:00
-- url     : https://prove2.me/theorems/9377c723-8dbd-4b34-a778-e969fd9b96b6
-- title:
--   Sum of the nonnegative integers below 1044
-- statement:
--   The sum of the integers from $0$ through $1043$ equals $544446$, which is the triangular number $\\frac{1044(1043)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1044 : ∑ k ∈ range 1044, k = 544446 := by sorry
end FiniteTriangular
