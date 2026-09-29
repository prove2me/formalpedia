-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1113
-- name    : FiniteTriangular.sum_range_1113
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:56.104039+00:00
-- url     : https://prove2.me/theorems/04de61f4-7e3c-450f-b5a9-8230d481167c
-- title:
--   Sum of the nonnegative integers below 1113
-- statement:
--   The sum of the integers from $0$ through $1112$ equals $618828$, which is the triangular number $\\frac{1113(1112)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1113 : ∑ k ∈ range 1113, k = 618828 := by sorry
end FiniteTriangular
