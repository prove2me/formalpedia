-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_834
-- name    : FiniteTriangular.sum_range_834
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:06.567405+00:00
-- url     : https://prove2.me/theorems/69f1c325-cea9-4af5-9c0b-6f8e8221bb44
-- title:
--   Sum of integers below 834
-- statement:
--   The sum of the nonnegative integers strictly less than $834$ equals $347361$. Equivalently, $\\sum_{k=0}^{834-1} k = 834(834-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_834 : ∑ k ∈ range 834, k = 347361 := by sorry

end FiniteTriangular
