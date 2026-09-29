-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_762
-- name    : FiniteTriangular.sum_range_762
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:38.542468+00:00
-- url     : https://prove2.me/theorems/dd3b8e56-ac76-4774-ba88-bc4f48010da1
-- title:
--   Sum of integers below 762
-- statement:
--   The sum of the nonnegative integers strictly less than $762$ equals $289941$. Equivalently, $\\sum_{k=0}^{762-1} k = 762(762-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_762 : ∑ k ∈ range 762, k = 289941 := by sorry

end FiniteTriangular
