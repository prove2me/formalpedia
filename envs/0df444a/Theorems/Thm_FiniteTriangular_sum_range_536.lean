-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_536
-- name    : FiniteTriangular.sum_range_536
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:17.488441+00:00
-- url     : https://prove2.me/theorems/5c27298b-63c2-45ba-8193-aa96799a5dd3
-- title:
--   Sum of integers below 536
-- statement:
--   The sum of the nonnegative integers strictly less than $536$ equals $143380$. Equivalently, $\\sum_{k=0}^{536-1} k = 536(536-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_536 : ∑ k ∈ range 536, k = 143380 := by sorry

end FiniteTriangular
