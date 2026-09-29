-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1032
-- name    : FiniteTriangular.sum_range_1032
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:45.619987+00:00
-- url     : https://prove2.me/theorems/750d411b-a5b3-4a7c-a121-e8539011aaab
-- title:
--   Sum of the nonnegative integers below 1032
-- statement:
--   The sum of the integers from $0$ through $1031$ equals $531996$, which is the triangular number $\\frac{1032(1031)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1032 : ∑ k ∈ range 1032, k = 531996 := by sorry
end FiniteTriangular
