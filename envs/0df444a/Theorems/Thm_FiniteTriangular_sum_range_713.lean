-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_713
-- name    : FiniteTriangular.sum_range_713
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:41.994544+00:00
-- url     : https://prove2.me/theorems/22849a17-87ae-4412-bd87-2ba50882f470
-- title:
--   Sum of integers below 713
-- statement:
--   The sum of the nonnegative integers strictly less than $713$ equals $253828$. Equivalently, $\\sum_{k=0}^{713-1} k = 713(713-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_713 : ∑ k ∈ range 713, k = 253828 := by sorry

end FiniteTriangular
