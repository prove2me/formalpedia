-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1024
-- name    : FiniteTriangular.sum_range_1024
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:05.511993+00:00
-- url     : https://prove2.me/theorems/28b6fc28-8b21-4586-8a8c-c5ffe6615cd1
-- title:
--   Sum of the nonnegative integers below 1024
-- statement:
--   The sum of the integers from $0$ through $1023$ equals $523776$, which is the triangular number $\\frac{1024(1023)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1024 : ∑ k ∈ range 1024, k = 523776 := by sorry
end FiniteTriangular
