-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_479
-- name    : FiniteTriangular.sum_range_479
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:30.613699+00:00
-- url     : https://prove2.me/theorems/ef3cd417-4a8f-46a4-bf9a-3592862bb9dc
-- title:
--   Sum of integers below 479
-- statement:
--   The sum of the nonnegative integers strictly less than $479$ equals $114481$. Equivalently, $\\sum_{k=0}^{479-1} k = 479(479-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_479 : ∑ k ∈ range 479, k = 114481 := by sorry

end FiniteTriangular
