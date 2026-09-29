-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_628
-- name    : FiniteTriangular.sum_range_628
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:51.310511+00:00
-- url     : https://prove2.me/theorems/c550e4fc-1f60-45be-88e6-00296e1cbfa7
-- title:
--   Sum of integers below 628
-- statement:
--   The sum of the nonnegative integers strictly less than $628$ equals $196878$. Equivalently, $\\sum_{k=0}^{628-1} k = 628(628-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_628 : ∑ k ∈ range 628, k = 196878 := by sorry

end FiniteTriangular
