-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1011
-- name    : FiniteTriangular.sum_range_1011
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:19.802987+00:00
-- url     : https://prove2.me/theorems/dd5459ed-e268-4b83-b951-5fd6a1fd58ac
-- title:
--   Sum of the nonnegative integers below 1011
-- statement:
--   The sum of the integers from $0$ through $1010$ equals $510555$, which is the triangular number $\\frac{1011(1010)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1011 : ∑ k ∈ range 1011, k = 510555 := by sorry
end FiniteTriangular
