-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_998
-- name    : FiniteTriangular.sum_range_998
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:43.417928+00:00
-- url     : https://prove2.me/theorems/2c9cc7da-ee88-4e38-a512-f2b6f71360bc
-- title:
--   Sum of the nonnegative integers below 998
-- statement:
--   The sum of the integers from $0$ through $997$ equals $497503$, which is the triangular number $\\frac{998(997)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_998 : ∑ k ∈ range 998, k = 497503 := by sorry
end FiniteTriangular
