-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_499
-- name    : FiniteTriangular.sum_range_499
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:25.436742+00:00
-- url     : https://prove2.me/theorems/746e8e82-8543-42fd-94e3-22e1eb4034de
-- title:
--   Sum of integers below 499
-- statement:
--   The sum of the nonnegative integers strictly less than $499$ equals $124251$. Equivalently, $\\sum_{k=0}^{499-1} k = 499(499-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_499 : ∑ k ∈ range 499, k = 124251 := by sorry

end FiniteTriangular
