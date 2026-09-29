-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_248
-- name    : FiniteTriangular.sum_range_248
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:14.575158+00:00
-- url     : https://prove2.me/theorems/0ca060b2-2977-4fda-b241-9374ff39de0b
-- title:
--   Sum of integers below 248
-- statement:
--   The sum of the nonnegative integers strictly less than $248$ equals $30628$. Equivalently, $\\sum_{k=0}^{248-1} k = 248(248-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_248 : ∑ k ∈ range 248, k = 30628 := by sorry

end FiniteTriangular
