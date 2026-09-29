-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1010
-- name    : FiniteTriangular.sum_range_1010
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:16.307619+00:00
-- url     : https://prove2.me/theorems/cdf9b1df-1480-4ad8-8370-10debd15bdd1
-- title:
--   Sum of the nonnegative integers below 1010
-- statement:
--   The sum of the integers from $0$ through $1009$ equals $509545$, which is the triangular number $\\frac{1010(1009)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1010 : ∑ k ∈ range 1010, k = 509545 := by sorry
end FiniteTriangular
