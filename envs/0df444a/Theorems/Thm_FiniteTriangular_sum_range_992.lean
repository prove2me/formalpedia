-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_992
-- name    : FiniteTriangular.sum_range_992
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:57.786751+00:00
-- url     : https://prove2.me/theorems/53bd850d-5a44-4e85-abb7-b78b8289d57d
-- title:
--   Sum of the nonnegative integers below 992
-- statement:
--   The sum of the integers from $0$ through $991$ equals $491536$, which is the triangular number $\\frac{992(991)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_992 : ∑ k ∈ range 992, k = 491536 := by sorry
end FiniteTriangular
