-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_627
-- name    : FiniteTriangular.sum_range_627
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:51.947265+00:00
-- url     : https://prove2.me/theorems/571c35f1-4402-4577-a9ef-4652cfaf27a3
-- title:
--   Sum of integers below 627
-- statement:
--   The sum of the nonnegative integers strictly less than $627$ equals $196251$. Equivalently, $\\sum_{k=0}^{627-1} k = 627(627-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_627 : ∑ k ∈ range 627, k = 196251 := by sorry

end FiniteTriangular
