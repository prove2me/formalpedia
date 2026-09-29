-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_841
-- name    : FiniteTriangular.sum_range_841
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:45.981183+00:00
-- url     : https://prove2.me/theorems/cfb45cbf-77e5-460f-aa3c-c26d92f2aef2
-- title:
--   Sum of integers below 841
-- statement:
--   The sum of the nonnegative integers strictly less than $841$ equals $353220$. Equivalently, $\\sum_{k=0}^{841-1} k = 841(841-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_841 : ∑ k ∈ range 841, k = 353220 := by sorry

end FiniteTriangular
