-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_869
-- name    : FiniteTriangular.sum_range_869
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:48.046308+00:00
-- url     : https://prove2.me/theorems/0893ae5d-172f-4d92-a925-87fc3f64dc23
-- title:
--   Sum of integers below 869
-- statement:
--   The sum of the nonnegative integers strictly less than $869$ equals $377146$. Equivalently, $\\sum_{k=0}^{869-1} k = 869(869-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_869 : ∑ k ∈ range 869, k = 377146 := by sorry

end FiniteTriangular
