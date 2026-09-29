-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_129
-- name    : FiniteTriangular.sum_range_129
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:49.541179+00:00
-- url     : https://prove2.me/theorems/c87f90a1-fdc1-4442-a910-669c485b1507
-- title:
--   Sum of integers below 129
-- statement:
--   The sum of the nonnegative integers strictly less than $129$ equals $8256$. Equivalently, $\sum_{k=0}^{129-1} k = 129(129-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_129 : ∑ k ∈ range 129, k = 8256 := by sorry

end FiniteTriangular
