-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_832
-- name    : FiniteTriangular.sum_range_832
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:29.13237+00:00
-- url     : https://prove2.me/theorems/ea207b28-7d5e-4470-a331-fa9845563255
-- title:
--   Sum of integers below 832
-- statement:
--   The sum of the nonnegative integers strictly less than $832$ equals $345696$. Equivalently, $\\sum_{k=0}^{832-1} k = 832(832-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_832 : ∑ k ∈ range 832, k = 345696 := by sorry

end FiniteTriangular
