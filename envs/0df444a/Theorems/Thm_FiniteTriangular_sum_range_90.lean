-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_90
-- name    : FiniteTriangular.sum_range_90
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:45.241982+00:00
-- url     : https://prove2.me/theorems/f5a593fd-5628-4c7c-a662-e3cba83084df
-- title:
--   Sum of integers below 90
-- statement:
--   The sum of the nonnegative integers strictly less than $90$ equals $4005$. Equivalently, $\sum_{k=0}^{90-1} k = 90(90-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_90 : ∑ k ∈ range 90, k = 4005 := by sorry

end FiniteTriangular
