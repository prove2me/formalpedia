-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_670
-- name    : FiniteTriangular.sum_range_670
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:13.153449+00:00
-- url     : https://prove2.me/theorems/9cc591ed-d66a-4a45-b15c-11d044267316
-- title:
--   Sum of integers below 670
-- statement:
--   The sum of the nonnegative integers strictly less than $670$ equals $224115$. Equivalently, $\\sum_{k=0}^{670-1} k = 670(670-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_670 : ∑ k ∈ range 670, k = 224115 := by sorry

end FiniteTriangular
