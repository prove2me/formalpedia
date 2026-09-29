-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_922
-- name    : FiniteTriangular.sum_range_922
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:33.930982+00:00
-- url     : https://prove2.me/theorems/744f8778-d832-4bd2-9db9-f2692cabad33
-- title:
--   Sum of integers below 922
-- statement:
--   The sum of the nonnegative integers strictly less than $922$ equals $424581$. Equivalently, $\\sum_{k=0}^{922-1} k = 922(922-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_922 : ∑ k ∈ range 922, k = 424581 := by sorry

end FiniteTriangular
