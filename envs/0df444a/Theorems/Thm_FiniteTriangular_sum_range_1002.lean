-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1002
-- name    : FiniteTriangular.sum_range_1002
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:32.444987+00:00
-- url     : https://prove2.me/theorems/02c644c6-70bc-48b2-ac80-0c62e9f9d932
-- title:
--   Sum of the nonnegative integers below 1002
-- statement:
--   The sum of the integers from $0$ through $1001$ equals $501501$, which is the triangular number $\\frac{1002(1001)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1002 : ∑ k ∈ range 1002, k = 501501 := by sorry
end FiniteTriangular
