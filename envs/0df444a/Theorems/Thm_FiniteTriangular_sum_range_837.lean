-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_837
-- name    : FiniteTriangular.sum_range_837
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:09.651034+00:00
-- url     : https://prove2.me/theorems/6461b3d0-e019-47a8-b727-58078de3deb8
-- title:
--   Sum of integers below 837
-- statement:
--   The sum of the nonnegative integers strictly less than $837$ equals $349866$. Equivalently, $\\sum_{k=0}^{837-1} k = 837(837-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_837 : ∑ k ∈ range 837, k = 349866 := by sorry

end FiniteTriangular
