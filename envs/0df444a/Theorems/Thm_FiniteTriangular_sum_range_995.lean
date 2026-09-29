-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_995
-- name    : FiniteTriangular.sum_range_995
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:36.749971+00:00
-- url     : https://prove2.me/theorems/fa9bb400-9bfa-489c-b418-6784b8b602da
-- title:
--   Sum of the nonnegative integers below 995
-- statement:
--   The sum of the integers from $0$ through $994$ equals $494515$, which is the triangular number $\\frac{995(994)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_995 : ∑ k ∈ range 995, k = 494515 := by sorry
end FiniteTriangular
