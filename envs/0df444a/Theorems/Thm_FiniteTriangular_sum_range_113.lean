-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_113
-- name    : FiniteTriangular.sum_range_113
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:04.75667+00:00
-- url     : https://prove2.me/theorems/61257ae9-8b1c-4671-89bc-8120dacc54d6
-- title:
--   Sum of integers below 113
-- statement:
--   The sum of the nonnegative integers strictly less than $113$ equals $6328$. Equivalently, $\sum_{k=0}^{113-1} k = 113(113-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_113 : ∑ k ∈ range 113, k = 6328 := by sorry

end FiniteTriangular
