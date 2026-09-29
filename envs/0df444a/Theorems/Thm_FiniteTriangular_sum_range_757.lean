-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_757
-- name    : FiniteTriangular.sum_range_757
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:56.973294+00:00
-- url     : https://prove2.me/theorems/ed552d77-bbc5-4be7-945e-b4e95f689c26
-- title:
--   Sum of integers below 757
-- statement:
--   The sum of the nonnegative integers strictly less than $757$ equals $286146$. Equivalently, $\\sum_{k=0}^{757-1} k = 757(757-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_757 : ∑ k ∈ range 757, k = 286146 := by sorry

end FiniteTriangular
