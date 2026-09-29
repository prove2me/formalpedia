-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1021
-- name    : FiniteTriangular.sum_range_1021
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:00.885709+00:00
-- url     : https://prove2.me/theorems/e763554f-46cb-43fa-ad61-f4f1cf616005
-- title:
--   Sum of the nonnegative integers below 1021
-- statement:
--   The sum of the integers from $0$ through $1020$ equals $520710$, which is the triangular number $\\frac{1021(1020)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1021 : ∑ k ∈ range 1021, k = 520710 := by sorry
end FiniteTriangular
