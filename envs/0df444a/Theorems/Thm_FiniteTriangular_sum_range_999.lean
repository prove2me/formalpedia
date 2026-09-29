-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_999
-- name    : FiniteTriangular.sum_range_999
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:37.493001+00:00
-- url     : https://prove2.me/theorems/e76d09a4-5b99-4cf0-854e-254e2867ad8c
-- title:
--   Sum of the nonnegative integers below 999
-- statement:
--   The sum of the integers from $0$ through $998$ equals $498501$, which is the triangular number $\\frac{999(998)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_999 : ∑ k ∈ range 999, k = 498501 := by sorry
end FiniteTriangular
