-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_182
-- name    : FiniteTriangular.sum_range_182
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:01.932173+00:00
-- url     : https://prove2.me/theorems/4b6933a1-5b4e-4255-bb15-0859bb6db154
-- title:
--   Sum of integers below 182
-- statement:
--   The sum of the nonnegative integers strictly less than $182$ equals $16471$. Equivalently, $\sum_{k=0}^{182-1} k = 182(182-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_182 : ∑ k ∈ range 182, k = 16471 := by sorry

end FiniteTriangular
