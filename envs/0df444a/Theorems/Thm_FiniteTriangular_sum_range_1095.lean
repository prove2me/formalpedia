-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1095
-- name    : FiniteTriangular.sum_range_1095
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:53.747264+00:00
-- url     : https://prove2.me/theorems/d5c16e48-effc-4a66-b910-6c48bca31658
-- title:
--   Sum of the nonnegative integers below 1095
-- statement:
--   The sum of the integers from $0$ through $1094$ equals $598965$, which is the triangular number $\\frac{1095(1094)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1095 : ∑ k ∈ range 1095, k = 598965 := by sorry
end FiniteTriangular
