-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1049
-- name    : FiniteTriangular.sum_range_1049
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:51.544013+00:00
-- url     : https://prove2.me/theorems/6e19b6d7-cb0e-4303-be77-ba7cac5e9e7f
-- title:
--   Sum of the nonnegative integers below 1049
-- statement:
--   The sum of the integers from $0$ through $1048$ equals $549676$, which is the triangular number $\\frac{1049(1048)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1049 : ∑ k ∈ range 1049, k = 549676 := by sorry
end FiniteTriangular
