-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_60
-- name    : FiniteTriangular.sum_range_60
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:17.371984+00:00
-- url     : https://prove2.me/theorems/9e814c5e-7844-4de2-8650-ce6207baa25f
-- title:
--   Sum of integers below 60
-- statement:
--   The sum of the nonnegative integers strictly less than $60$ equals $1770$. Equivalently, $\sum_{k=0}^{60-1} k = 60(60-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_60 : ∑ k ∈ range 60, k = 1770 := by sorry

end FiniteTriangular
