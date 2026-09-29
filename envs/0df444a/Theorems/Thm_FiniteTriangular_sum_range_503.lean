-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_503
-- name    : FiniteTriangular.sum_range_503
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:23.449744+00:00
-- url     : https://prove2.me/theorems/0f0be143-b591-4443-8ad1-6134decdea45
-- title:
--   Sum of integers below 503
-- statement:
--   The sum of the nonnegative integers strictly less than $503$ equals $126253$. Equivalently, $\\sum_{k=0}^{503-1} k = 503(503-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_503 : ∑ k ∈ range 503, k = 126253 := by sorry

end FiniteTriangular
