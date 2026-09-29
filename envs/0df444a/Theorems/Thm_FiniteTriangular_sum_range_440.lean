-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_440
-- name    : FiniteTriangular.sum_range_440
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:26.382732+00:00
-- url     : https://prove2.me/theorems/fa123c09-2410-43d5-8dbe-e7beb598fb23
-- title:
--   Sum of integers below 440
-- statement:
--   The sum of the nonnegative integers strictly less than $440$ equals $96580$. Equivalently, $\\sum_{k=0}^{440-1} k = 440(440-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_440 : ∑ k ∈ range 440, k = 96580 := by sorry

end FiniteTriangular
