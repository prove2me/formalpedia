-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_484
-- name    : FiniteTriangular.sum_range_484
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:11.711982+00:00
-- url     : https://prove2.me/theorems/0709d356-9d71-4693-b2c1-db6d0faff0da
-- title:
--   Sum of integers below 484
-- statement:
--   The sum of the nonnegative integers strictly less than $484$ equals $116886$. Equivalently, $\\sum_{k=0}^{484-1} k = 484(484-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_484 : ∑ k ∈ range 484, k = 116886 := by sorry

end FiniteTriangular
