-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_988
-- name    : FiniteTriangular.sum_range_988
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:54.922975+00:00
-- url     : https://prove2.me/theorems/6eddd17c-2a5f-4c31-a47a-e6e5489ab388
-- title:
--   Sum of the nonnegative integers below 988
-- statement:
--   The sum of the integers from $0$ through $987$ equals $487578$, which is the triangular number $\\frac{988(987)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_988 : ∑ k ∈ range 988, k = 487578 := by sorry
end FiniteTriangular
