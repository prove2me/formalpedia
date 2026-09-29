-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_945
-- name    : FiniteTriangular.sum_range_945
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:53.899838+00:00
-- url     : https://prove2.me/theorems/1cf3d643-d176-4a34-aa9f-e917025c6ee5
-- title:
--   Sum of integers below 945
-- statement:
--   The sum of the nonnegative integers strictly less than $945$ equals $446040$. Equivalently, $\\sum_{k=0}^{945-1} k = 945(945-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_945 : ∑ k ∈ range 945, k = 446040 := by sorry

end FiniteTriangular
