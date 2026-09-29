-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_43
-- name    : FiniteTriangular.sum_range_43
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:08.575987+00:00
-- url     : https://prove2.me/theorems/128fdff8-5241-4aa4-94ad-7c2ca3c75fe0
-- title:
--   Sum of integers below 43
-- statement:
--   The sum of the nonnegative integers strictly less than $43$ equals $903$. Equivalently, $\sum_{k=0}^{43-1} k = 43(43-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_43 : ∑ k ∈ range 43, k = 903 := by sorry

end FiniteTriangular
