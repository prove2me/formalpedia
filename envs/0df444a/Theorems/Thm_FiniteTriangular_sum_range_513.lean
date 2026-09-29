-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_513
-- name    : FiniteTriangular.sum_range_513
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:56.05775+00:00
-- url     : https://prove2.me/theorems/4241c1f2-2c35-4ae8-aae2-0fb5e97fd343
-- title:
--   Sum of integers below 513
-- statement:
--   The sum of the nonnegative integers strictly less than $513$ equals $131328$. Equivalently, $\\sum_{k=0}^{513-1} k = 513(513-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_513 : ∑ k ∈ range 513, k = 131328 := by sorry

end FiniteTriangular
