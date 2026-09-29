-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_920
-- name    : FiniteTriangular.sum_range_920
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:47.528514+00:00
-- url     : https://prove2.me/theorems/b1432a71-0c59-48b5-8d04-dd9b8eb3b4e5
-- title:
--   Sum of integers below 920
-- statement:
--   The sum of the nonnegative integers strictly less than $920$ equals $422740$. Equivalently, $\\sum_{k=0}^{920-1} k = 920(920-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_920 : ∑ k ∈ range 920, k = 422740 := by sorry

end FiniteTriangular
