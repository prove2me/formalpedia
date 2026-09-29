-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_787
-- name    : FiniteTriangular.sum_range_787
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:53.766641+00:00
-- url     : https://prove2.me/theorems/10c7b512-e849-4875-8d09-c06d05c108f7
-- title:
--   Sum of integers below 787
-- statement:
--   The sum of the nonnegative integers strictly less than $787$ equals $309291$. Equivalently, $\\sum_{k=0}^{787-1} k = 787(787-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_787 : ∑ k ∈ range 787, k = 309291 := by sorry

end FiniteTriangular
