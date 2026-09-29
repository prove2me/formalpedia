-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_420
-- name    : FiniteTriangular.sum_range_420
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:53.335401+00:00
-- url     : https://prove2.me/theorems/3d970999-6328-40ce-995f-ccc2045518b6
-- title:
--   Sum of integers below 420
-- statement:
--   The sum of the nonnegative integers strictly less than $420$ equals $87990$. Equivalently, $\\sum_{k=0}^{420-1} k = 420(420-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_420 : ∑ k ∈ range 420, k = 87990 := by sorry

end FiniteTriangular
