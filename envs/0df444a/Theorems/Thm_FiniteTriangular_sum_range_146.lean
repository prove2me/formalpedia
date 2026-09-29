-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_146
-- name    : FiniteTriangular.sum_range_146
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:13.233917+00:00
-- url     : https://prove2.me/theorems/0dbb4004-aef8-4cfc-94dc-51a52b9d0948
-- title:
--   Sum of integers below 146
-- statement:
--   The sum of the nonnegative integers strictly less than $146$ equals $10585$. Equivalently, $\sum_{k=0}^{146-1} k = 146(146-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_146 : ∑ k ∈ range 146, k = 10585 := by sorry

end FiniteTriangular
