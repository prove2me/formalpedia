-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_505
-- name    : FiniteTriangular.sum_range_505
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:10.982383+00:00
-- url     : https://prove2.me/theorems/7183374b-11ad-4379-957d-8f4582fed847
-- title:
--   Sum of integers below 505
-- statement:
--   The sum of the nonnegative integers strictly less than $505$ equals $127260$. Equivalently, $\\sum_{k=0}^{505-1} k = 505(505-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_505 : ∑ k ∈ range 505, k = 127260 := by sorry

end FiniteTriangular
