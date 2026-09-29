-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_669
-- name    : FiniteTriangular.sum_range_669
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:14.985727+00:00
-- url     : https://prove2.me/theorems/d6010f55-25b6-4a28-8c96-cd0d117b3856
-- title:
--   Sum of integers below 669
-- statement:
--   The sum of the nonnegative integers strictly less than $669$ equals $223446$. Equivalently, $\\sum_{k=0}^{669-1} k = 669(669-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_669 : ∑ k ∈ range 669, k = 223446 := by sorry

end FiniteTriangular
