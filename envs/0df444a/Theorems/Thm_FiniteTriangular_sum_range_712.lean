-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_712
-- name    : FiniteTriangular.sum_range_712
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:06:47.345121+00:00
-- url     : https://prove2.me/theorems/9eda9f10-a5e8-4dc8-b407-7d0c1d33a65e
-- title:
--   Sum of integers below 712
-- statement:
--   The sum of the nonnegative integers strictly less than $712$ equals $253116$. Equivalently, $\\sum_{k=0}^{712-1} k = 712(712-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_712 : ∑ k ∈ range 712, k = 253116 := by sorry

end FiniteTriangular
