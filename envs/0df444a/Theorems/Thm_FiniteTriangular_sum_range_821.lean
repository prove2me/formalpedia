-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_821
-- name    : FiniteTriangular.sum_range_821
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:41.701526+00:00
-- url     : https://prove2.me/theorems/db1afa39-ef09-4be6-a532-695a55d648a8
-- title:
--   Sum of integers below 821
-- statement:
--   The sum of the nonnegative integers strictly less than $821$ equals $336610$. Equivalently, $\\sum_{k=0}^{821-1} k = 821(821-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_821 : ∑ k ∈ range 821, k = 336610 := by sorry

end FiniteTriangular
