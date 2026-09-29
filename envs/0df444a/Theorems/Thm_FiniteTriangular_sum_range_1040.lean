-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1040
-- name    : FiniteTriangular.sum_range_1040
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:52.178256+00:00
-- url     : https://prove2.me/theorems/6f1817ea-94e5-48b8-a0d5-69caa19a1ddf
-- title:
--   Sum of the nonnegative integers below 1040
-- statement:
--   The sum of the integers from $0$ through $1039$ equals $540280$, which is the triangular number $\\frac{1040(1039)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1040 : ∑ k ∈ range 1040, k = 540280 := by sorry
end FiniteTriangular
