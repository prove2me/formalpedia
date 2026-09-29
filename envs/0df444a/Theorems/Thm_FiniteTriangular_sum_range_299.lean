-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_299
-- name    : FiniteTriangular.sum_range_299
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:52.173915+00:00
-- url     : https://prove2.me/theorems/15391de5-6676-4ae9-a7a9-7b8ac4274b03
-- title:
--   Sum of integers below 299
-- statement:
--   The sum of the nonnegative integers strictly less than $299$ equals $44551$. Equivalently, $\\sum_{k=0}^{299-1} k = 299(299-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_299 : ∑ k ∈ range 299, k = 44551 := by sorry

end FiniteTriangular
