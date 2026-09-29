-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_765
-- name    : FiniteTriangular.sum_range_765
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:36.824124+00:00
-- url     : https://prove2.me/theorems/26febb7b-fa34-48a7-a30a-539ab262e460
-- title:
--   Sum of integers below 765
-- statement:
--   The sum of the nonnegative integers strictly less than $765$ equals $292230$. Equivalently, $\\sum_{k=0}^{765-1} k = 765(765-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_765 : ∑ k ∈ range 765, k = 292230 := by sorry

end FiniteTriangular
