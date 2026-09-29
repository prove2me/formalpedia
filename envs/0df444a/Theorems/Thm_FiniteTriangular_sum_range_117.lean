-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_117
-- name    : FiniteTriangular.sum_range_117
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:09.033316+00:00
-- url     : https://prove2.me/theorems/d59db55c-d6ec-4c73-80cd-71e9dfaf5911
-- title:
--   Sum of integers below 117
-- statement:
--   The sum of the nonnegative integers strictly less than $117$ equals $6786$. Equivalently, $\sum_{k=0}^{117-1} k = 117(117-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_117 : ∑ k ∈ range 117, k = 6786 := by sorry

end FiniteTriangular
