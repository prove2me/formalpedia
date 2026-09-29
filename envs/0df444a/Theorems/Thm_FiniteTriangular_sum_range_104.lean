-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_104
-- name    : FiniteTriangular.sum_range_104
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:21.035463+00:00
-- url     : https://prove2.me/theorems/ff303f1f-cfb9-4801-8458-735f8a4402c2
-- title:
--   Sum of integers below 104
-- statement:
--   The sum of the nonnegative integers strictly less than $104$ equals $5356$. Equivalently, $\sum_{k=0}^{104-1} k = 104(104-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_104 : ∑ k ∈ range 104, k = 5356 := by sorry

end FiniteTriangular
