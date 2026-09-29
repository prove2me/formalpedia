-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_588
-- name    : FiniteTriangular.sum_range_588
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:20.678986+00:00
-- url     : https://prove2.me/theorems/c732dc94-62ae-4837-ba16-2fe2b1e051b3
-- title:
--   Sum of integers below 588
-- statement:
--   The sum of the nonnegative integers strictly less than $588$ equals $172578$. Equivalently, $\\sum_{k=0}^{588-1} k = 588(588-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_588 : ∑ k ∈ range 588, k = 172578 := by sorry

end FiniteTriangular
