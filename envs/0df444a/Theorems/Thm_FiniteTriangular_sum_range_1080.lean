-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1080
-- name    : FiniteTriangular.sum_range_1080
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:25.259179+00:00
-- url     : https://prove2.me/theorems/bcd0be2d-7163-44e6-92c8-7d31636d9c08
-- title:
--   Sum of the nonnegative integers below 1080
-- statement:
--   The sum of the integers from $0$ through $1079$ equals $582660$, which is the triangular number $\\frac{1080(1079)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1080 : ∑ k ∈ range 1080, k = 582660 := by sorry
end FiniteTriangular
