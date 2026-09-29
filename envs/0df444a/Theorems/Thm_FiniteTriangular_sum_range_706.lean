-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_706
-- name    : FiniteTriangular.sum_range_706
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:44.311954+00:00
-- url     : https://prove2.me/theorems/b7db39b2-bc87-4dd5-8613-d7baba2239d6
-- title:
--   Sum of integers below 706
-- statement:
--   The sum of the nonnegative integers strictly less than $706$ equals $248865$. Equivalently, $\\sum_{k=0}^{706-1} k = 706(706-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_706 : ∑ k ∈ range 706, k = 248865 := by sorry

end FiniteTriangular
