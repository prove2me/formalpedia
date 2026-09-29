-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_62
-- name    : FiniteTriangular.sum_range_62
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:14.537475+00:00
-- url     : https://prove2.me/theorems/961493d0-0c85-4734-baf2-ef71d384eb91
-- title:
--   Sum of integers below 62
-- statement:
--   The sum of the nonnegative integers strictly less than $62$ equals $1891$. Equivalently, $\sum_{k=0}^{62-1} k = 62(62-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_62 : ∑ k ∈ range 62, k = 1891 := by sorry

end FiniteTriangular
