-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_206
-- name    : FiniteTriangular.sum_range_206
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:17.288907+00:00
-- url     : https://prove2.me/theorems/8127dea8-5dbf-49c6-aea5-a811b3ee2aec
-- title:
--   Sum of integers below 206
-- statement:
--   The sum of the nonnegative integers strictly less than $206$ equals $21115$. Equivalently, $\\sum_{k=0}^{206-1} k = 206(206-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_206 : ∑ k ∈ range 206, k = 21115 := by sorry

end FiniteTriangular
