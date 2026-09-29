-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_983
-- name    : FiniteTriangular.sum_range_983
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:03.807309+00:00
-- url     : https://prove2.me/theorems/36b89a9d-f582-4422-99e5-31e74ed29d5d
-- title:
--   Sum of the nonnegative integers below 983
-- statement:
--   The sum of the integers from $0$ through $982$ equals $482653$, which is the triangular number $\\frac{983(982)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_983 : ∑ k ∈ range 983, k = 482653 := by sorry
end FiniteTriangular
