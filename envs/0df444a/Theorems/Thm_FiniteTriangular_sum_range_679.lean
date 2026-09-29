-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_679
-- name    : FiniteTriangular.sum_range_679
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:58.816772+00:00
-- url     : https://prove2.me/theorems/6e5ae4ed-a648-45cc-b05a-03ef4acaa5a7
-- title:
--   Sum of integers below 679
-- statement:
--   The sum of the nonnegative integers strictly less than $679$ equals $230181$. Equivalently, $\\sum_{k=0}^{679-1} k = 679(679-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_679 : ∑ k ∈ range 679, k = 230181 := by sorry

end FiniteTriangular
