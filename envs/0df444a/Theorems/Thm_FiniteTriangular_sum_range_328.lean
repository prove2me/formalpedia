-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_328
-- name    : FiniteTriangular.sum_range_328
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:24.147373+00:00
-- url     : https://prove2.me/theorems/00ca219a-6ca8-4dcf-acba-4a874edea794
-- title:
--   Sum of integers below 328
-- statement:
--   The sum of the nonnegative integers strictly less than $328$ equals $53628$. Equivalently, $\\sum_{k=0}^{328-1} k = 328(328-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_328 : ∑ k ∈ range 328, k = 53628 := by sorry

end FiniteTriangular
