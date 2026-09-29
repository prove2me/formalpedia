-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_111
-- name    : FiniteTriangular.sum_range_111
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:16.634979+00:00
-- url     : https://prove2.me/theorems/c1d03cef-aed1-414b-80ae-fcc6884e65c4
-- title:
--   Sum of integers below 111
-- statement:
--   The sum of the nonnegative integers strictly less than $111$ equals $6105$. Equivalently, $\sum_{k=0}^{111-1} k = 111(111-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_111 : ∑ k ∈ range 111, k = 6105 := by sorry

end FiniteTriangular
