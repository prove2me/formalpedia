-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_240
-- name    : FiniteTriangular.sum_range_240
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:37.397655+00:00
-- url     : https://prove2.me/theorems/51954280-70f5-4199-a550-8fd57a5c2887
-- title:
--   Sum of integers below 240
-- statement:
--   The sum of the nonnegative integers strictly less than $240$ equals $28680$. Equivalently, $\\sum_{k=0}^{240-1} k = 240(240-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_240 : ∑ k ∈ range 240, k = 28680 := by sorry

end FiniteTriangular
