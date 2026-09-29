-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_849
-- name    : FiniteTriangular.sum_range_849
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:19.591908+00:00
-- url     : https://prove2.me/theorems/0f9083e3-acc0-4349-b173-0ec10e2ffe10
-- title:
--   Sum of integers below 849
-- statement:
--   The sum of the nonnegative integers strictly less than $849$ equals $359976$. Equivalently, $\\sum_{k=0}^{849-1} k = 849(849-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_849 : ∑ k ∈ range 849, k = 359976 := by sorry

end FiniteTriangular
