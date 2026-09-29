-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_576
-- name    : FiniteTriangular.sum_range_576
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:54.219333+00:00
-- url     : https://prove2.me/theorems/ebaef069-f732-471c-9007-189c5ca09d3e
-- title:
--   Sum of integers below 576
-- statement:
--   The sum of the nonnegative integers strictly less than $576$ equals $165600$. Equivalently, $\\sum_{k=0}^{576-1} k = 576(576-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_576 : ∑ k ∈ range 576, k = 165600 := by sorry

end FiniteTriangular
