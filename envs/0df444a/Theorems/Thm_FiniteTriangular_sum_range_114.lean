-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_114
-- name    : FiniteTriangular.sum_range_114
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:09.424583+00:00
-- url     : https://prove2.me/theorems/5d7cb1c1-ee9f-48b8-b0ad-33ad4474a04a
-- title:
--   Sum of integers below 114
-- statement:
--   The sum of the nonnegative integers strictly less than $114$ equals $6441$. Equivalently, $\sum_{k=0}^{114-1} k = 114(114-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_114 : ∑ k ∈ range 114, k = 6441 := by sorry

end FiniteTriangular
