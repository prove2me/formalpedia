-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_443
-- name    : FiniteTriangular.sum_range_443
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:07.385986+00:00
-- url     : https://prove2.me/theorems/28714dea-cbb3-4fbf-b914-e3337c9b6b13
-- title:
--   Sum of integers below 443
-- statement:
--   The sum of the nonnegative integers strictly less than $443$ equals $97903$. Equivalently, $\\sum_{k=0}^{443-1} k = 443(443-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_443 : ∑ k ∈ range 443, k = 97903 := by sorry

end FiniteTriangular
