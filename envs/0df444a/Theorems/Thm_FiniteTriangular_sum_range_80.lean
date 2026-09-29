-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_80
-- name    : FiniteTriangular.sum_range_80
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:09.536912+00:00
-- url     : https://prove2.me/theorems/29df5f6d-6db3-4940-8fb2-04ddabc4d2c0
-- title:
--   Sum of integers below 80
-- statement:
--   The sum of the nonnegative integers strictly less than $80$ equals $3160$. Equivalently, $\sum_{k=0}^{80-1} k = 80(80-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_80 : ∑ k ∈ range 80, k = 3160 := by sorry

end FiniteTriangular
