-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_66
-- name    : FiniteTriangular.sum_range_66
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:47.313458+00:00
-- url     : https://prove2.me/theorems/b4ef5b78-63ee-435c-bafc-a9f9f1cbfd4e
-- title:
--   Sum of integers below 66
-- statement:
--   The sum of the nonnegative integers strictly less than $66$ equals $2145$. Equivalently, $\sum_{k=0}^{66-1} k = 66(66-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_66 : ∑ k ∈ range 66, k = 2145 := by sorry

end FiniteTriangular
