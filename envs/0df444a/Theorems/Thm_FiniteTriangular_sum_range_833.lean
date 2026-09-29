-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_833
-- name    : FiniteTriangular.sum_range_833
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:08.408453+00:00
-- url     : https://prove2.me/theorems/ba6d1afc-6d71-4908-910a-9d414b4c277a
-- title:
--   Sum of integers below 833
-- statement:
--   The sum of the nonnegative integers strictly less than $833$ equals $346528$. Equivalently, $\\sum_{k=0}^{833-1} k = 833(833-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_833 : ∑ k ∈ range 833, k = 346528 := by sorry

end FiniteTriangular
