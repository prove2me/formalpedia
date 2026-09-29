-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_589
-- name    : FiniteTriangular.sum_range_589
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:24.972984+00:00
-- url     : https://prove2.me/theorems/60ded6fe-0620-4900-ba3b-7d2a26a24761
-- title:
--   Sum of integers below 589
-- statement:
--   The sum of the nonnegative integers strictly less than $589$ equals $173166$. Equivalently, $\\sum_{k=0}^{589-1} k = 589(589-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_589 : ∑ k ∈ range 589, k = 173166 := by sorry

end FiniteTriangular
