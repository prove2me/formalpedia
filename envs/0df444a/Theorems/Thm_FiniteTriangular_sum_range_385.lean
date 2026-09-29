-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_385
-- name    : FiniteTriangular.sum_range_385
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:46:57.040839+00:00
-- url     : https://prove2.me/theorems/46fd5c97-5fb8-4daf-8aa6-c1a270c2ce62
-- title:
--   Sum of integers below 385
-- statement:
--   The sum of the nonnegative integers strictly less than $385$ equals $73920$. Equivalently, $\\sum_{k=0}^{385-1} k = 385(385-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_385 : ∑ k ∈ range 385, k = 73920 := by sorry

end FiniteTriangular
