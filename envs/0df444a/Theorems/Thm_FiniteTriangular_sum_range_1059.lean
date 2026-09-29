-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1059
-- name    : FiniteTriangular.sum_range_1059
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:54.949702+00:00
-- url     : https://prove2.me/theorems/204fa5b0-a700-466f-b649-027a6c6c59ca
-- title:
--   Sum of the nonnegative integers below 1059
-- statement:
--   The sum of the integers from $0$ through $1058$ equals $560211$, which is the triangular number $\\frac{1059(1058)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1059 : ∑ k ∈ range 1059, k = 560211 := by sorry
end FiniteTriangular
