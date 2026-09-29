-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_291
-- name    : FiniteTriangular.sum_range_291
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:05.48487+00:00
-- url     : https://prove2.me/theorems/d4124608-a2ba-4041-b987-06438bb550dc
-- title:
--   Sum of integers below 291
-- statement:
--   The sum of the nonnegative integers strictly less than $291$ equals $42195$. Equivalently, $\\sum_{k=0}^{291-1} k = 291(291-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_291 : ∑ k ∈ range 291, k = 42195 := by sorry

end FiniteTriangular
