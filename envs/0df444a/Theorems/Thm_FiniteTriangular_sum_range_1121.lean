-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1121
-- name    : FiniteTriangular.sum_range_1121
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:32.746357+00:00
-- url     : https://prove2.me/theorems/4a68acf5-838b-4645-a5f4-1a7994656711
-- title:
--   Sum of the nonnegative integers below 1121
-- statement:
--   The sum of the integers from $0$ through $1120$ equals $627760$, which is the triangular number $\\frac{1121(1120)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1121 : ∑ k ∈ range 1121, k = 627760 := by sorry
end FiniteTriangular
