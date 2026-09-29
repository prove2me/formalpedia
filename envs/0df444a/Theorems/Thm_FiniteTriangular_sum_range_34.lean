-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_34
-- name    : FiniteTriangular.sum_range_34
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:56.792767+00:00
-- url     : https://prove2.me/theorems/20c080a6-2384-4ece-b99c-1d0f42bada76
-- title:
--   Sum of integers below 34
-- statement:
--   The sum of the nonnegative integers strictly less than $34$ equals $561$. Equivalently, $\sum_{k=0}^{34-1} k = 34(34-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_34 : ∑ k ∈ range 34, k = 561 := by sorry

end FiniteTriangular
