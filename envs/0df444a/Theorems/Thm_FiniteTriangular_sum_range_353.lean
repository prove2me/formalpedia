-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_353
-- name    : FiniteTriangular.sum_range_353
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:39:15.928274+00:00
-- url     : https://prove2.me/theorems/4a3f7680-84e5-4046-b97e-920b3dc3c5c6
-- title:
--   Sum of integers below 353
-- statement:
--   The sum of the nonnegative integers strictly less than $353$ equals $62128$. Equivalently, $\\sum_{k=0}^{353-1} k = 353(353-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_353 : ∑ k ∈ range 353, k = 62128 := by sorry

end FiniteTriangular
