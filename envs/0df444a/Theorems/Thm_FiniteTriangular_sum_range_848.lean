-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_848
-- name    : FiniteTriangular.sum_range_848
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:43.97561+00:00
-- url     : https://prove2.me/theorems/5ca03e9d-8a9b-45b0-8422-55e34012ed21
-- title:
--   Sum of integers below 848
-- statement:
--   The sum of the nonnegative integers strictly less than $848$ equals $359128$. Equivalently, $\\sum_{k=0}^{848-1} k = 848(848-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_848 : ∑ k ∈ range 848, k = 359128 := by sorry

end FiniteTriangular
