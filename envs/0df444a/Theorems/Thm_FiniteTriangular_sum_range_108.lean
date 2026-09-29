-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_108
-- name    : FiniteTriangular.sum_range_108
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:14.577489+00:00
-- url     : https://prove2.me/theorems/b928ad66-9f00-4202-b32c-b3b1a89b78d8
-- title:
--   Sum of integers below 108
-- statement:
--   The sum of the nonnegative integers strictly less than $108$ equals $5778$. Equivalently, $\sum_{k=0}^{108-1} k = 108(108-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_108 : ∑ k ∈ range 108, k = 5778 := by sorry

end FiniteTriangular
