-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1015
-- name    : FiniteTriangular.sum_range_1015
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:20.849986+00:00
-- url     : https://prove2.me/theorems/a1da3e5c-6dcf-410e-9f84-8eb01bffe24e
-- title:
--   Sum of the nonnegative integers below 1015
-- statement:
--   The sum of the integers from $0$ through $1014$ equals $514605$, which is the triangular number $\\frac{1015(1014)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1015 : ∑ k ∈ range 1015, k = 514605 := by sorry
end FiniteTriangular
