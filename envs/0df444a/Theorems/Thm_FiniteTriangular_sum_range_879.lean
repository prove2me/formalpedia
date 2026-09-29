-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_879
-- name    : FiniteTriangular.sum_range_879
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:32.299506+00:00
-- url     : https://prove2.me/theorems/a8d6c124-d0c8-4624-9447-c058522e9a68
-- title:
--   Sum of integers below 879
-- statement:
--   The sum of the nonnegative integers strictly less than $879$ equals $385881$. Equivalently, $\\sum_{k=0}^{879-1} k = 879(879-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_879 : ∑ k ∈ range 879, k = 385881 := by sorry

end FiniteTriangular
