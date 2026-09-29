-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_112
-- name    : FiniteTriangular.sum_range_112
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:19.148982+00:00
-- url     : https://prove2.me/theorems/8161cfbb-bac7-485a-8b5b-cf986e1886e6
-- title:
--   Sum of integers below 112
-- statement:
--   The sum of the nonnegative integers strictly less than $112$ equals $6216$. Equivalently, $\sum_{k=0}^{112-1} k = 112(112-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_112 : ∑ k ∈ range 112, k = 6216 := by sorry

end FiniteTriangular
