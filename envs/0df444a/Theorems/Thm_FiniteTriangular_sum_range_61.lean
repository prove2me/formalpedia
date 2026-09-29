-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_61
-- name    : FiniteTriangular.sum_range_61
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:18.172331+00:00
-- url     : https://prove2.me/theorems/bba19729-d7fa-468c-a8e5-f07859de3ec3
-- title:
--   Sum of integers below 61
-- statement:
--   The sum of the nonnegative integers strictly less than $61$ equals $1830$. Equivalently, $\sum_{k=0}^{61-1} k = 61(61-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_61 : ∑ k ∈ range 61, k = 1830 := by sorry

end FiniteTriangular
