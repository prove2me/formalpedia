-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1028
-- name    : FiniteTriangular.sum_range_1028
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:47.660862+00:00
-- url     : https://prove2.me/theorems/3f061b93-968a-46f7-be9c-7185f3df896b
-- title:
--   Sum of the nonnegative integers below 1028
-- statement:
--   The sum of the integers from $0$ through $1027$ equals $527878$, which is the triangular number $\\frac{1028(1027)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1028 : ∑ k ∈ range 1028, k = 527878 := by sorry
end FiniteTriangular
