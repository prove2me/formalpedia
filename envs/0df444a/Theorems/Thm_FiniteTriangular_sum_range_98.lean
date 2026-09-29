-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_98
-- name    : FiniteTriangular.sum_range_98
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:23.187245+00:00
-- url     : https://prove2.me/theorems/1765868f-79dc-49d5-93fd-5b1ec831fcb4
-- title:
--   Sum of integers below 98
-- statement:
--   The sum of the nonnegative integers strictly less than $98$ equals $4753$. Equivalently, $\sum_{k=0}^{98-1} k = 98(98-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_98 : ∑ k ∈ range 98, k = 4753 := by sorry

end FiniteTriangular
