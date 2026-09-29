-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_336
-- name    : FiniteTriangular.sum_range_336
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:08.545531+00:00
-- url     : https://prove2.me/theorems/d9dd6def-4c25-447f-91ae-7ee049738ce3
-- title:
--   Sum of integers below 336
-- statement:
--   The sum of the nonnegative integers strictly less than $336$ equals $56280$. Equivalently, $\\sum_{k=0}^{336-1} k = 336(336-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_336 : ∑ k ∈ range 336, k = 56280 := by sorry

end FiniteTriangular
