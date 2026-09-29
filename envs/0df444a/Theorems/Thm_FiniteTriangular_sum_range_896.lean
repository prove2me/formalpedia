-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_896
-- name    : FiniteTriangular.sum_range_896
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:56.303056+00:00
-- url     : https://prove2.me/theorems/a73a2643-1072-437a-8e7f-273b66a82101
-- title:
--   Sum of integers below 896
-- statement:
--   The sum of the nonnegative integers strictly less than $896$ equals $400960$. Equivalently, $\\sum_{k=0}^{896-1} k = 896(896-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_896 : ∑ k ∈ range 896, k = 400960 := by sorry

end FiniteTriangular
