-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_36
-- name    : FiniteTriangular.sum_range_36
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:54.963926+00:00
-- url     : https://prove2.me/theorems/678927b7-724d-47d0-94d6-339182732a90
-- title:
--   Sum of integers below 36
-- statement:
--   The sum of the nonnegative integers strictly less than $36$ equals $630$. Equivalently, $\sum_{k=0}^{36-1} k = 36(36-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_36 : ∑ k ∈ range 36, k = 630 := by sorry

end FiniteTriangular
