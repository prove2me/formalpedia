-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_548
-- name    : FiniteTriangular.sum_range_548
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:47.161587+00:00
-- url     : https://prove2.me/theorems/d3d6523f-e1ac-4a15-be81-6a0ed5331b02
-- title:
--   Sum of integers below 548
-- statement:
--   The sum of the nonnegative integers strictly less than $548$ equals $149878$. Equivalently, $\\sum_{k=0}^{548-1} k = 548(548-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_548 : ∑ k ∈ range 548, k = 149878 := by sorry

end FiniteTriangular
