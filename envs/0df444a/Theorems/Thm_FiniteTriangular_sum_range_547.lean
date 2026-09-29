-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_547
-- name    : FiniteTriangular.sum_range_547
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:46.305734+00:00
-- url     : https://prove2.me/theorems/dd89d743-713f-4a66-a560-b765adb46365
-- title:
--   Sum of integers below 547
-- statement:
--   The sum of the nonnegative integers strictly less than $547$ equals $149331$. Equivalently, $\\sum_{k=0}^{547-1} k = 547(547-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_547 : ∑ k ∈ range 547, k = 149331 := by sorry

end FiniteTriangular
