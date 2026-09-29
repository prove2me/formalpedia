-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_798
-- name    : FiniteTriangular.sum_range_798
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:31.943921+00:00
-- url     : https://prove2.me/theorems/aa8ca494-7514-4a4f-b429-810119491661
-- title:
--   Sum of integers below 798
-- statement:
--   The sum of the nonnegative integers strictly less than $798$ equals $318003$. Equivalently, $\\sum_{k=0}^{798-1} k = 798(798-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_798 : ∑ k ∈ range 798, k = 318003 := by sorry

end FiniteTriangular
