-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_852
-- name    : FiniteTriangular.sum_range_852
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:19.672186+00:00
-- url     : https://prove2.me/theorems/11683e9f-6ebf-4b9e-8fc7-986f3b65a823
-- title:
--   Sum of integers below 852
-- statement:
--   The sum of the nonnegative integers strictly less than $852$ equals $362526$. Equivalently, $\\sum_{k=0}^{852-1} k = 852(852-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_852 : ∑ k ∈ range 852, k = 362526 := by sorry

end FiniteTriangular
