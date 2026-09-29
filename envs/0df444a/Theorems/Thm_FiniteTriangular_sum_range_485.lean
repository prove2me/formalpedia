-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_485
-- name    : FiniteTriangular.sum_range_485
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:09.736415+00:00
-- url     : https://prove2.me/theorems/6074dfa8-d71c-48b4-96c2-056be6aefdf4
-- title:
--   Sum of integers below 485
-- statement:
--   The sum of the nonnegative integers strictly less than $485$ equals $117370$. Equivalently, $\\sum_{k=0}^{485-1} k = 485(485-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_485 : ∑ k ∈ range 485, k = 117370 := by sorry

end FiniteTriangular
