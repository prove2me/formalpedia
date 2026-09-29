-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_437
-- name    : FiniteTriangular.sum_range_437
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:25.438819+00:00
-- url     : https://prove2.me/theorems/ced58f72-6cf3-4046-9429-8d0d87f0176c
-- title:
--   Sum of integers below 437
-- statement:
--   The sum of the nonnegative integers strictly less than $437$ equals $95266$. Equivalently, $\\sum_{k=0}^{437-1} k = 437(437-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_437 : ∑ k ∈ range 437, k = 95266 := by sorry

end FiniteTriangular
