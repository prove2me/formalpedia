-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_160
-- name    : FiniteTriangular.sum_range_160
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:21.500121+00:00
-- url     : https://prove2.me/theorems/3ee89d70-4fe7-498c-9450-3caaa4ee032f
-- title:
--   Sum of integers below 160
-- statement:
--   The sum of the nonnegative integers strictly less than $160$ equals $12720$. Equivalently, $\sum_{k=0}^{160-1} k = 160(160-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_160 : ∑ k ∈ range 160, k = 12720 := by sorry

end FiniteTriangular
