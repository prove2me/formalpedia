-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_28
-- name    : FiniteTriangular.sum_range_28
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:13:07.964007+00:00
-- url     : https://prove2.me/theorems/cbf78722-7d13-46ce-a387-afe6ee549f53
-- title:
--   Sum of integers below 28
-- statement:
--   The sum of the nonnegative integers strictly less than $28$ equals $378$. Equivalently, $\sum_{k=0}^{28-1} k = 28(28-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_28 : ∑ k ∈ range 28, k = 378 := by sorry

end FiniteTriangular
