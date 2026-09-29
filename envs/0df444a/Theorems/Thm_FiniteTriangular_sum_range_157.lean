-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_157
-- name    : FiniteTriangular.sum_range_157
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:20.905509+00:00
-- url     : https://prove2.me/theorems/c469ef81-efce-4c7c-b511-5fc06d2d1d10
-- title:
--   Sum of integers below 157
-- statement:
--   The sum of the nonnegative integers strictly less than $157$ equals $12246$. Equivalently, $\sum_{k=0}^{157-1} k = 157(157-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_157 : ∑ k ∈ range 157, k = 12246 := by sorry

end FiniteTriangular
