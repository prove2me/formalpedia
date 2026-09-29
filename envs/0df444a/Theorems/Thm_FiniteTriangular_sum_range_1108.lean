-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1108
-- name    : FiniteTriangular.sum_range_1108
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:26.523786+00:00
-- url     : https://prove2.me/theorems/b21604d3-0345-427a-917b-3f46742a2df0
-- title:
--   Sum of the nonnegative integers below 1108
-- statement:
--   The sum of the integers from $0$ through $1107$ equals $613278$, which is the triangular number $\\frac{1108(1107)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1108 : ∑ k ∈ range 1108, k = 613278 := by sorry
end FiniteTriangular
