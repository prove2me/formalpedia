-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_202
-- name    : FiniteTriangular.sum_range_202
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:19.587614+00:00
-- url     : https://prove2.me/theorems/1800445a-7e49-4de7-919e-77fb72b80ad0
-- title:
--   Sum of integers below 202
-- statement:
--   The sum of the nonnegative integers strictly less than $202$ equals $20301$. Equivalently, $\\sum_{k=0}^{202-1} k = 202(202-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_202 : ∑ k ∈ range 202, k = 20301 := by sorry

end FiniteTriangular
