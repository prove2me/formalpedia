-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1085
-- name    : FiniteTriangular.sum_range_1085
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:21.088226+00:00
-- url     : https://prove2.me/theorems/5b9c9ed9-9b68-4cc3-b9c3-4a9fb097503b
-- title:
--   Sum of the nonnegative integers below 1085
-- statement:
--   The sum of the integers from $0$ through $1084$ equals $588070$, which is the triangular number $\\frac{1085(1084)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1085 : ∑ k ∈ range 1085, k = 588070 := by sorry
end FiniteTriangular
