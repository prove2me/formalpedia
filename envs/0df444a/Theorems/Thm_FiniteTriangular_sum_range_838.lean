-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_838
-- name    : FiniteTriangular.sum_range_838
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:10.030723+00:00
-- url     : https://prove2.me/theorems/39bd5c7e-dc00-4b41-9839-5cbf98ec692d
-- title:
--   Sum of integers below 838
-- statement:
--   The sum of the nonnegative integers strictly less than $838$ equals $350703$. Equivalently, $\\sum_{k=0}^{838-1} k = 838(838-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_838 : ∑ k ∈ range 838, k = 350703 := by sorry

end FiniteTriangular
