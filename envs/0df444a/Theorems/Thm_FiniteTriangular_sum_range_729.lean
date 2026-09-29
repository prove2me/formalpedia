-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_729
-- name    : FiniteTriangular.sum_range_729
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:34.488118+00:00
-- url     : https://prove2.me/theorems/751a8cd4-5e91-4eee-b3c8-73c21777f878
-- title:
--   Sum of integers below 729
-- statement:
--   The sum of the nonnegative integers strictly less than $729$ equals $265356$. Equivalently, $\\sum_{k=0}^{729-1} k = 729(729-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_729 : ∑ k ∈ range 729, k = 265356 := by sorry

end FiniteTriangular
