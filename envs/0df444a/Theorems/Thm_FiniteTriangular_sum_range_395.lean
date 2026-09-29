-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_395
-- name    : FiniteTriangular.sum_range_395
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:41.936979+00:00
-- url     : https://prove2.me/theorems/291b31d1-7e39-4a15-8809-c8d120fbdd28
-- title:
--   Sum of integers below 395
-- statement:
--   The sum of the nonnegative integers strictly less than $395$ equals $77815$. Equivalently, $\\sum_{k=0}^{395-1} k = 395(395-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_395 : ∑ k ∈ range 395, k = 77815 := by sorry

end FiniteTriangular
