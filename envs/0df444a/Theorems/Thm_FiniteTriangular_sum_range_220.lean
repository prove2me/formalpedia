-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_220
-- name    : FiniteTriangular.sum_range_220
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:16.099979+00:00
-- url     : https://prove2.me/theorems/b2af46a8-f6f5-40f8-9db7-26a8054b203a
-- title:
--   Sum of integers below 220
-- statement:
--   The sum of the nonnegative integers strictly less than $220$ equals $24090$. Equivalently, $\\sum_{k=0}^{220-1} k = 220(220-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_220 : ∑ k ∈ range 220, k = 24090 := by sorry

end FiniteTriangular
