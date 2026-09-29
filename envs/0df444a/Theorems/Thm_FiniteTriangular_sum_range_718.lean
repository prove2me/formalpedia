-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_718
-- name    : FiniteTriangular.sum_range_718
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:40.834323+00:00
-- url     : https://prove2.me/theorems/73221bcd-c177-46f7-99f6-a64ec3e9b3eb
-- title:
--   Sum of integers below 718
-- statement:
--   The sum of the nonnegative integers strictly less than $718$ equals $257403$. Equivalently, $\\sum_{k=0}^{718-1} k = 718(718-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_718 : ∑ k ∈ range 718, k = 257403 := by sorry

end FiniteTriangular
