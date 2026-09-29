-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_148
-- name    : FiniteTriangular.sum_range_148
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:12.124001+00:00
-- url     : https://prove2.me/theorems/195239b1-a2cb-4e30-8ed7-f7409c0bcecd
-- title:
--   Sum of integers below 148
-- statement:
--   The sum of the nonnegative integers strictly less than $148$ equals $10878$. Equivalently, $\sum_{k=0}^{148-1} k = 148(148-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_148 : ∑ k ∈ range 148, k = 10878 := by sorry

end FiniteTriangular
