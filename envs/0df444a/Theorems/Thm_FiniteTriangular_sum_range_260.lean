-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_260
-- name    : FiniteTriangular.sum_range_260
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:02.218493+00:00
-- url     : https://prove2.me/theorems/67c13d7d-7c98-4c59-b66d-57595298ebc3
-- title:
--   Sum of integers below 260
-- statement:
--   The sum of the nonnegative integers strictly less than $260$ equals $33670$. Equivalently, $\\sum_{k=0}^{260-1} k = 260(260-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_260 : ∑ k ∈ range 260, k = 33670 := by sorry

end FiniteTriangular
