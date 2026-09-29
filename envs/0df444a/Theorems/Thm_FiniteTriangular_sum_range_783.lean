-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_783
-- name    : FiniteTriangular.sum_range_783
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:10.763963+00:00
-- url     : https://prove2.me/theorems/298b28ec-a4b1-4fd3-949b-09282d4c54a9
-- title:
--   Sum of integers below 783
-- statement:
--   The sum of the nonnegative integers strictly less than $783$ equals $306153$. Equivalently, $\\sum_{k=0}^{783-1} k = 783(783-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_783 : ∑ k ∈ range 783, k = 306153 := by sorry

end FiniteTriangular
