-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_155
-- name    : FiniteTriangular.sum_range_155
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:22.61915+00:00
-- url     : https://prove2.me/theorems/7643ead0-092a-4e5f-8862-e8f380fff119
-- title:
--   Sum of integers below 155
-- statement:
--   The sum of the nonnegative integers strictly less than $155$ equals $11935$. Equivalently, $\sum_{k=0}^{155-1} k = 155(155-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_155 : ∑ k ∈ range 155, k = 11935 := by sorry

end FiniteTriangular
