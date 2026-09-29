-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_742
-- name    : FiniteTriangular.sum_range_742
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:30.849921+00:00
-- url     : https://prove2.me/theorems/f309490a-f7c2-475a-8560-eef51df4f0fd
-- title:
--   Sum of integers below 742
-- statement:
--   The sum of the nonnegative integers strictly less than $742$ equals $274911$. Equivalently, $\\sum_{k=0}^{742-1} k = 742(742-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_742 : ∑ k ∈ range 742, k = 274911 := by sorry

end FiniteTriangular
