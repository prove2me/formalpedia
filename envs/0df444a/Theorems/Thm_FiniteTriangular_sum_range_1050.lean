-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1050
-- name    : FiniteTriangular.sum_range_1050
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:53.640291+00:00
-- url     : https://prove2.me/theorems/56799f3a-0bde-4901-9e3b-7c8a78c79eb7
-- title:
--   Sum of the nonnegative integers below 1050
-- statement:
--   The sum of the integers from $0$ through $1049$ equals $550725$, which is the triangular number $\\frac{1050(1049)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1050 : ∑ k ∈ range 1050, k = 550725 := by sorry
end FiniteTriangular
