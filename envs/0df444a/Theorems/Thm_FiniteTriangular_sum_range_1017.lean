-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1017
-- name    : FiniteTriangular.sum_range_1017
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:02.25999+00:00
-- url     : https://prove2.me/theorems/9c94ce0e-8547-49a3-ba0c-f29e0020e037
-- title:
--   Sum of the nonnegative integers below 1017
-- statement:
--   The sum of the integers from $0$ through $1016$ equals $516636$, which is the triangular number $\\frac{1017(1016)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1017 : ∑ k ∈ range 1017, k = 516636 := by sorry
end FiniteTriangular
