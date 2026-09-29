-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_435
-- name    : FiniteTriangular.sum_range_435
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:22.772122+00:00
-- url     : https://prove2.me/theorems/4495a92d-ed74-4630-ae1c-07c5139dca10
-- title:
--   Sum of integers below 435
-- statement:
--   The sum of the nonnegative integers strictly less than $435$ equals $94395$. Equivalently, $\\sum_{k=0}^{435-1} k = 435(435-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_435 : ∑ k ∈ range 435, k = 94395 := by sorry

end FiniteTriangular
