-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1064
-- name    : FiniteTriangular.sum_range_1064
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:55.681796+00:00
-- url     : https://prove2.me/theorems/5413ef33-89d7-48e7-ad01-f23b4fae2101
-- title:
--   Sum of the nonnegative integers below 1064
-- statement:
--   The sum of the integers from $0$ through $1063$ equals $565516$, which is the triangular number $\\frac{1064(1063)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1064 : ∑ k ∈ range 1064, k = 565516 := by sorry
end FiniteTriangular
