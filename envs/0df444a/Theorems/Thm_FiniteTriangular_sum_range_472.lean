-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_472
-- name    : FiniteTriangular.sum_range_472
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:40.72017+00:00
-- url     : https://prove2.me/theorems/d545fcfd-a94a-4231-b895-41423ea8dfbb
-- title:
--   Sum of integers below 472
-- statement:
--   The sum of the nonnegative integers strictly less than $472$ equals $111156$. Equivalently, $\\sum_{k=0}^{472-1} k = 472(472-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_472 : ∑ k ∈ range 472, k = 111156 := by sorry

end FiniteTriangular
