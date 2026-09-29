-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_705
-- name    : FiniteTriangular.sum_range_705
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:48.271426+00:00
-- url     : https://prove2.me/theorems/08242b98-67b3-4bc9-80b9-60a5c582a35c
-- title:
--   Sum of integers below 705
-- statement:
--   The sum of the nonnegative integers strictly less than $705$ equals $248160$. Equivalently, $\\sum_{k=0}^{705-1} k = 705(705-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_705 : ∑ k ∈ range 705, k = 248160 := by sorry

end FiniteTriangular
