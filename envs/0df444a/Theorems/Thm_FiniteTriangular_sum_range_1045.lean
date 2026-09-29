-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1045
-- name    : FiniteTriangular.sum_range_1045
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:13.189871+00:00
-- url     : https://prove2.me/theorems/c97cafea-1ac3-4102-9514-009c10af70a2
-- title:
--   Sum of the nonnegative integers below 1045
-- statement:
--   The sum of the integers from $0$ through $1044$ equals $545490$, which is the triangular number $\\frac{1045(1044)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1045 : ∑ k ∈ range 1045, k = 545490 := by sorry
end FiniteTriangular
