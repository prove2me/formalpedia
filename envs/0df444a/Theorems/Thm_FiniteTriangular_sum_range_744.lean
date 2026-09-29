-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_744
-- name    : FiniteTriangular.sum_range_744
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:32.60548+00:00
-- url     : https://prove2.me/theorems/5b219911-41b4-418e-92ab-6d91e46826e5
-- title:
--   Sum of integers below 744
-- statement:
--   The sum of the nonnegative integers strictly less than $744$ equals $276396$. Equivalently, $\\sum_{k=0}^{744-1} k = 744(744-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_744 : ∑ k ∈ range 744, k = 276396 := by sorry

end FiniteTriangular
