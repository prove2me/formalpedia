-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1008
-- name    : FiniteTriangular.sum_range_1008
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:44.578487+00:00
-- url     : https://prove2.me/theorems/daa65e61-7485-4b01-bb9d-ba61adc4e5a1
-- title:
--   Sum of the nonnegative integers below 1008
-- statement:
--   The sum of the integers from $0$ through $1007$ equals $507528$, which is the triangular number $\\frac{1008(1007)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1008 : ∑ k ∈ range 1008, k = 507528 := by sorry
end FiniteTriangular
