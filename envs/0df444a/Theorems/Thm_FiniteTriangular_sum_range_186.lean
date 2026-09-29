-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_186
-- name    : FiniteTriangular.sum_range_186
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:05.686446+00:00
-- url     : https://prove2.me/theorems/9231b460-ffd6-4718-8c1a-df0377f1a85d
-- title:
--   Sum of integers below 186
-- statement:
--   The sum of the nonnegative integers strictly less than $186$ equals $17205$. Equivalently, $\\sum_{k=0}^{186-1} k = 186(186-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_186 : ∑ k ∈ range 186, k = 17205 := by sorry

end FiniteTriangular
