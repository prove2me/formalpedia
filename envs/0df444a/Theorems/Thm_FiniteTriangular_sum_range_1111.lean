-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1111
-- name    : FiniteTriangular.sum_range_1111
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:25.905698+00:00
-- url     : https://prove2.me/theorems/cb27cb74-bc89-495d-a4b3-6c9520129e0e
-- title:
--   Sum of the nonnegative integers below 1111
-- statement:
--   The sum of the integers from $0$ through $1110$ equals $616605$, which is the triangular number $\\frac{1111(1110)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1111 : ∑ k ∈ range 1111, k = 616605 := by sorry
end FiniteTriangular
