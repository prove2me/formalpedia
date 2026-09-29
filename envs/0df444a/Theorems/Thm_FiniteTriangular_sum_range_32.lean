-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_32
-- name    : FiniteTriangular.sum_range_32
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:09.226294+00:00
-- url     : https://prove2.me/theorems/0c00ea01-5db2-4563-8b37-002fd6b79ca5
-- title:
--   Sum of integers below 32
-- statement:
--   The sum of the nonnegative integers strictly less than $32$ equals $496$. Equivalently, $\sum_{k=0}^{32-1} k = 32(32-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_32 : ∑ k ∈ range 32, k = 496 := by sorry

end FiniteTriangular
