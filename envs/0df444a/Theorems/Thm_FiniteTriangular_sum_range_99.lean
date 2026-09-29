-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_99
-- name    : FiniteTriangular.sum_range_99
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:27.083772+00:00
-- url     : https://prove2.me/theorems/cc521e7e-93c1-4a07-a1e0-b3cac3ab1a78
-- title:
--   Sum of integers below 99
-- statement:
--   The sum of the nonnegative integers strictly less than $99$ equals $4851$. Equivalently, $\sum_{k=0}^{99-1} k = 99(99-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_99 : ∑ k ∈ range 99, k = 4851 := by sorry

end FiniteTriangular
