-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_784
-- name    : FiniteTriangular.sum_range_784
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:23:13.365994+00:00
-- url     : https://prove2.me/theorems/08ca2101-3d37-4c51-9cc3-0c32a0e37fa4
-- title:
--   Sum of integers below 784
-- statement:
--   The sum of the nonnegative integers strictly less than $784$ equals $306936$. Equivalently, $\\sum_{k=0}^{784-1} k = 784(784-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_784 : ∑ k ∈ range 784, k = 306936 := by sorry

end FiniteTriangular
