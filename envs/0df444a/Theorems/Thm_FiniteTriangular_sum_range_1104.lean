-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1104
-- name    : FiniteTriangular.sum_range_1104
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:37.787193+00:00
-- url     : https://prove2.me/theorems/181a00ac-eb7e-4c1b-b09d-54629f1238eb
-- title:
--   Sum of the nonnegative integers below 1104
-- statement:
--   The sum of the integers from $0$ through $1103$ equals $608856$, which is the triangular number $\\frac{1104(1103)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1104 : ∑ k ∈ range 1104, k = 608856 := by sorry
end FiniteTriangular
