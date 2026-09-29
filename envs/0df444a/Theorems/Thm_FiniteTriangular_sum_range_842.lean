-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_842
-- name    : FiniteTriangular.sum_range_842
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:46.019676+00:00
-- url     : https://prove2.me/theorems/dedbb74b-115f-47df-86d1-4ebcdff59de7
-- title:
--   Sum of integers below 842
-- statement:
--   The sum of the nonnegative integers strictly less than $842$ equals $354061$. Equivalently, $\\sum_{k=0}^{842-1} k = 842(842-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_842 : ∑ k ∈ range 842, k = 354061 := by sorry

end FiniteTriangular
