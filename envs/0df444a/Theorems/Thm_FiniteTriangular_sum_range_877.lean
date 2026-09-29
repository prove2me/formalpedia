-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_877
-- name    : FiniteTriangular.sum_range_877
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:31.633419+00:00
-- url     : https://prove2.me/theorems/708accbc-8743-4016-bb4a-3b9519a604a6
-- title:
--   Sum of integers below 877
-- statement:
--   The sum of the nonnegative integers strictly less than $877$ equals $384126$. Equivalently, $\\sum_{k=0}^{877-1} k = 877(877-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_877 : ∑ k ∈ range 877, k = 384126 := by sorry

end FiniteTriangular
