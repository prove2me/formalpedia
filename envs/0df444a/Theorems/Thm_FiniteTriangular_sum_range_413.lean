-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_413
-- name    : FiniteTriangular.sum_range_413
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:06.870018+00:00
-- url     : https://prove2.me/theorems/dd146431-eaca-4bb6-9f56-d8b36bbe42f5
-- title:
--   Sum of integers below 413
-- statement:
--   The sum of the nonnegative integers strictly less than $413$ equals $85078$. Equivalently, $\\sum_{k=0}^{413-1} k = 413(413-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_413 : ∑ k ∈ range 413, k = 85078 := by sorry

end FiniteTriangular
