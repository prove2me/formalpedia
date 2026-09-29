-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_657
-- name    : FiniteTriangular.sum_range_657
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:35.074764+00:00
-- url     : https://prove2.me/theorems/f14749c4-b6b6-4c21-a4c1-cdaf8e46abb4
-- title:
--   Sum of integers below 657
-- statement:
--   The sum of the nonnegative integers strictly less than $657$ equals $215496$. Equivalently, $\\sum_{k=0}^{657-1} k = 657(657-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_657 : ∑ k ∈ range 657, k = 215496 := by sorry

end FiniteTriangular
