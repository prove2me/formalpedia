-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_984
-- name    : FiniteTriangular.sum_range_984
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:05.170465+00:00
-- url     : https://prove2.me/theorems/c1e4e13a-6967-48ce-b53b-bba0600d6a65
-- title:
--   Sum of the nonnegative integers below 984
-- statement:
--   The sum of the integers from $0$ through $983$ equals $483636$, which is the triangular number $\\frac{984(983)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_984 : ∑ k ∈ range 984, k = 483636 := by sorry
end FiniteTriangular
