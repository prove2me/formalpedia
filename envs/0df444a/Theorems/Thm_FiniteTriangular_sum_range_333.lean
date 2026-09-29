-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_333
-- name    : FiniteTriangular.sum_range_333
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:07.548598+00:00
-- url     : https://prove2.me/theorems/3e3230b1-eba6-4441-b4d1-91105f72fd2f
-- title:
--   Sum of integers below 333
-- statement:
--   The sum of the nonnegative integers strictly less than $333$ equals $55278$. Equivalently, $\\sum_{k=0}^{333-1} k = 333(333-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_333 : ∑ k ∈ range 333, k = 55278 := by sorry

end FiniteTriangular
