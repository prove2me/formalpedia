-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_236
-- name    : FiniteTriangular.sum_range_236
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:33.714593+00:00
-- url     : https://prove2.me/theorems/012c90af-614f-4727-9bc1-a53cc0de85ac
-- title:
--   Sum of integers below 236
-- statement:
--   The sum of the nonnegative integers strictly less than $236$ equals $27730$. Equivalently, $\\sum_{k=0}^{236-1} k = 236(236-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_236 : ∑ k ∈ range 236, k = 27730 := by sorry

end FiniteTriangular
