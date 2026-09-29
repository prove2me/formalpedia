-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_930
-- name    : FiniteTriangular.sum_range_930
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:12.425584+00:00
-- url     : https://prove2.me/theorems/d559c3a6-afb7-48c6-b9ee-b4dd079ecb5a
-- title:
--   Sum of integers below 930
-- statement:
--   The sum of the nonnegative integers strictly less than $930$ equals $431985$. Equivalently, $\\sum_{k=0}^{930-1} k = 930(930-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_930 : ∑ k ∈ range 930, k = 431985 := by sorry

end FiniteTriangular
