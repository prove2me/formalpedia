-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_897
-- name    : FiniteTriangular.sum_range_897
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:31.874536+00:00
-- url     : https://prove2.me/theorems/cb62dd14-b73f-443d-ba34-f779f7f765d0
-- title:
--   Sum of integers below 897
-- statement:
--   The sum of the nonnegative integers strictly less than $897$ equals $401856$. Equivalently, $\\sum_{k=0}^{897-1} k = 897(897-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_897 : ∑ k ∈ range 897, k = 401856 := by sorry

end FiniteTriangular
