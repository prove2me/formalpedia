-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_755
-- name    : FiniteTriangular.sum_range_755
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:55.459105+00:00
-- url     : https://prove2.me/theorems/66c99064-6269-4eb1-877c-04aca7f0acd1
-- title:
--   Sum of integers below 755
-- statement:
--   The sum of the nonnegative integers strictly less than $755$ equals $284635$. Equivalently, $\\sum_{k=0}^{755-1} k = 755(755-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_755 : ∑ k ∈ range 755, k = 284635 := by sorry

end FiniteTriangular
