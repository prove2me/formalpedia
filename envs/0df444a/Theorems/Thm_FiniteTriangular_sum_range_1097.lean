-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1097
-- name    : FiniteTriangular.sum_range_1097
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:35.238345+00:00
-- url     : https://prove2.me/theorems/b1c417eb-884c-4d40-b7b9-cca330a10a79
-- title:
--   Sum of the nonnegative integers below 1097
-- statement:
--   The sum of the integers from $0$ through $1096$ equals $601156$, which is the triangular number $\\frac{1097(1096)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1097 : ∑ k ∈ range 1097, k = 601156 := by sorry
end FiniteTriangular
