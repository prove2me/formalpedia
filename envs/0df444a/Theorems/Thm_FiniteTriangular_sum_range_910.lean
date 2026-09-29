-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_910
-- name    : FiniteTriangular.sum_range_910
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:12.87552+00:00
-- url     : https://prove2.me/theorems/8a1bc963-0463-4dbd-a8ce-023a75d15b42
-- title:
--   Sum of integers below 910
-- statement:
--   The sum of the nonnegative integers strictly less than $910$ equals $413595$. Equivalently, $\\sum_{k=0}^{910-1} k = 910(910-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_910 : ∑ k ∈ range 910, k = 413595 := by sorry

end FiniteTriangular
