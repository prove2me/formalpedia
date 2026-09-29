-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1070
-- name    : FiniteTriangular.sum_range_1070
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:37.207086+00:00
-- url     : https://prove2.me/theorems/6663e19c-57bd-40ff-a2f8-b1fc3ee08732
-- title:
--   Sum of the nonnegative integers below 1070
-- statement:
--   The sum of the integers from $0$ through $1069$ equals $571915$, which is the triangular number $\\frac{1070(1069)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1070 : ∑ k ∈ range 1070, k = 571915 := by sorry
end FiniteTriangular
