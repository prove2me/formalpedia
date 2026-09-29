-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_295
-- name    : FiniteTriangular.sum_range_295
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:08.469091+00:00
-- url     : https://prove2.me/theorems/26e7beaa-59c1-4d53-a5a4-a5005c3e288b
-- title:
--   Sum of integers below 295
-- statement:
--   The sum of the nonnegative integers strictly less than $295$ equals $43365$. Equivalently, $\\sum_{k=0}^{295-1} k = 295(295-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_295 : ∑ k ∈ range 295, k = 43365 := by sorry

end FiniteTriangular
