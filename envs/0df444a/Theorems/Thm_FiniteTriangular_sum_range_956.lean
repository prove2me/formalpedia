-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_956
-- name    : FiniteTriangular.sum_range_956
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:43.671756+00:00
-- url     : https://prove2.me/theorems/1056ba14-aba4-400c-ad69-65411272a8c8
-- title:
--   Sum of integers below 956
-- statement:
--   The sum of the nonnegative integers strictly less than $956$ equals $456490$. Equivalently, $\\sum_{k=0}^{956-1} k = 956(956-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_956 : ∑ k ∈ range 956, k = 456490 := by sorry

end FiniteTriangular
