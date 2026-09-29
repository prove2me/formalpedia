-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_258
-- name    : FiniteTriangular.sum_range_258
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:04.403065+00:00
-- url     : https://prove2.me/theorems/4cf88141-c827-4b75-ada9-4f68d093ceef
-- title:
--   Sum of integers below 258
-- statement:
--   The sum of the nonnegative integers strictly less than $258$ equals $33153$. Equivalently, $\\sum_{k=0}^{258-1} k = 258(258-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_258 : ∑ k ∈ range 258, k = 33153 := by sorry

end FiniteTriangular
