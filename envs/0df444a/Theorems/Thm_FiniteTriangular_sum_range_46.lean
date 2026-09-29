-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_46
-- name    : FiniteTriangular.sum_range_46
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:08.933976+00:00
-- url     : https://prove2.me/theorems/3a7d047b-00c9-4c60-abdf-6d442ab2d09b
-- title:
--   Sum of integers below 46
-- statement:
--   The sum of the nonnegative integers strictly less than $46$ equals $1035$. Equivalently, $\sum_{k=0}^{46-1} k = 46(46-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_46 : ∑ k ∈ range 46, k = 1035 := by sorry

end FiniteTriangular
