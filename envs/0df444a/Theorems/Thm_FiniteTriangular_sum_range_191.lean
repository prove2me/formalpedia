-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_191
-- name    : FiniteTriangular.sum_range_191
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:12.178063+00:00
-- url     : https://prove2.me/theorems/e41b39ab-b6fd-4fe0-b4c9-c38c48b2dde5
-- title:
--   Sum of integers below 191
-- statement:
--   The sum of the nonnegative integers strictly less than $191$ equals $18145$. Equivalently, $\\sum_{k=0}^{191-1} k = 191(191-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_191 : ∑ k ∈ range 191, k = 18145 := by sorry

end FiniteTriangular
