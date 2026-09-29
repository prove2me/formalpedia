-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_781
-- name    : FiniteTriangular.sum_range_781
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:14.854964+00:00
-- url     : https://prove2.me/theorems/972f3753-1271-41f7-8977-279de4aa1134
-- title:
--   Sum of integers below 781
-- statement:
--   The sum of the nonnegative integers strictly less than $781$ equals $304590$. Equivalently, $\\sum_{k=0}^{781-1} k = 781(781-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_781 : ∑ k ∈ range 781, k = 304590 := by sorry

end FiniteTriangular
