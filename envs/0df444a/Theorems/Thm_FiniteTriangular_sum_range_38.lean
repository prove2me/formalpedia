-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_38
-- name    : FiniteTriangular.sum_range_38
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:54.616974+00:00
-- url     : https://prove2.me/theorems/5541826e-4f0e-41a4-be32-4f7325f7974e
-- title:
--   Sum of integers below 38
-- statement:
--   The sum of the nonnegative integers strictly less than $38$ equals $703$. Equivalently, $\sum_{k=0}^{38-1} k = 38(38-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_38 : ∑ k ∈ range 38, k = 703 := by sorry

end FiniteTriangular
