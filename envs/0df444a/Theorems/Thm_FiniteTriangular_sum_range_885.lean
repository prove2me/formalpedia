-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_885
-- name    : FiniteTriangular.sum_range_885
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:09.720625+00:00
-- url     : https://prove2.me/theorems/0000a17e-1f8b-4f5a-915c-dfea3ae511a9
-- title:
--   Sum of integers below 885
-- statement:
--   The sum of the nonnegative integers strictly less than $885$ equals $391170$. Equivalently, $\\sum_{k=0}^{885-1} k = 885(885-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_885 : ∑ k ∈ range 885, k = 391170 := by sorry

end FiniteTriangular
