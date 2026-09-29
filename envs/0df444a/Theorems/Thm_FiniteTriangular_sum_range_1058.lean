-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1058
-- name    : FiniteTriangular.sum_range_1058
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:37.163717+00:00
-- url     : https://prove2.me/theorems/c496d05c-7131-415c-9b70-3691ade82167
-- title:
--   Sum of the nonnegative integers below 1058
-- statement:
--   The sum of the integers from $0$ through $1057$ equals $559153$, which is the triangular number $\\frac{1058(1057)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1058 : ∑ k ∈ range 1058, k = 559153 := by sorry
end FiniteTriangular
