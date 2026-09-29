-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_948
-- name    : FiniteTriangular.sum_range_948
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:56.998625+00:00
-- url     : https://prove2.me/theorems/3b6e796a-a480-4fe8-b877-48ae6fadbd19
-- title:
--   Sum of integers below 948
-- statement:
--   The sum of the nonnegative integers strictly less than $948$ equals $448878$. Equivalently, $\\sum_{k=0}^{948-1} k = 948(948-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_948 : ∑ k ∈ range 948, k = 448878 := by sorry

end FiniteTriangular
