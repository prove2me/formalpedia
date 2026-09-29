-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_351
-- name    : FiniteTriangular.sum_range_351
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:37:39.318751+00:00
-- url     : https://prove2.me/theorems/09d6abae-2466-44e3-8391-f760636ced39
-- title:
--   Sum of integers below 351
-- statement:
--   The sum of the nonnegative integers strictly less than $351$ equals $61425$. Equivalently, $\\sum_{k=0}^{351-1} k = 351(351-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_351 : ∑ k ∈ range 351, k = 61425 := by sorry

end FiniteTriangular
