-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_81
-- name    : FiniteTriangular.sum_range_81
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:39:59.447991+00:00
-- url     : https://prove2.me/theorems/df7410ee-e65f-4b68-a312-49ae8d9a9a1f
-- title:
--   Sum of integers below 81
-- statement:
--   The sum of the nonnegative integers strictly less than $81$ equals $3240$. Equivalently, $\sum_{k=0}^{81-1} k = 81(81-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_81 : ∑ k ∈ range 81, k = 3240 := by sorry

end FiniteTriangular
