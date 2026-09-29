-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1053
-- name    : FiniteTriangular.sum_range_1053
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:53.220634+00:00
-- url     : https://prove2.me/theorems/80ef5802-a58e-4597-a436-f7289da05518
-- title:
--   Sum of the nonnegative integers below 1053
-- statement:
--   The sum of the integers from $0$ through $1052$ equals $553878$, which is the triangular number $\\frac{1053(1052)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1053 : ∑ k ∈ range 1053, k = 553878 := by sorry
end FiniteTriangular
