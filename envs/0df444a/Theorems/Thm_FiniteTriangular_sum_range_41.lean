-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_41
-- name    : FiniteTriangular.sum_range_41
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:56.056978+00:00
-- url     : https://prove2.me/theorems/363dbebc-ec7c-4ebb-8c1b-abe0aef02d9d
-- title:
--   Sum of integers below 41
-- statement:
--   The sum of the nonnegative integers strictly less than $41$ equals $820$. Equivalently, $\sum_{k=0}^{41-1} k = 41(41-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_41 : ∑ k ∈ range 41, k = 820 := by sorry

end FiniteTriangular
