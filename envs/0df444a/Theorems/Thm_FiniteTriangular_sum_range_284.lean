-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_284
-- name    : FiniteTriangular.sum_range_284
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:33.138127+00:00
-- url     : https://prove2.me/theorems/1ab6e844-4420-4518-abe9-2d59394a7c06
-- title:
--   Sum of integers below 284
-- statement:
--   The sum of the nonnegative integers strictly less than $284$ equals $40186$. Equivalently, $\\sum_{k=0}^{284-1} k = 284(284-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_284 : ∑ k ∈ range 284, k = 40186 := by sorry

end FiniteTriangular
