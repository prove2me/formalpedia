-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_611
-- name    : FiniteTriangular.sum_range_611
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:30.134572+00:00
-- url     : https://prove2.me/theorems/105193a5-6a45-4497-8f34-02153eb4833b
-- title:
--   Sum of integers below 611
-- statement:
--   The sum of the nonnegative integers strictly less than $611$ equals $186355$. Equivalently, $\\sum_{k=0}^{611-1} k = 611(611-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_611 : ∑ k ∈ range 611, k = 186355 := by sorry

end FiniteTriangular
