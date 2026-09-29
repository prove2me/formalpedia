-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_532
-- name    : FiniteTriangular.sum_range_532
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:20.312812+00:00
-- url     : https://prove2.me/theorems/b37632b7-142e-482b-ae02-bfe8e0e9d063
-- title:
--   Sum of integers below 532
-- statement:
--   The sum of the nonnegative integers strictly less than $532$ equals $141246$. Equivalently, $\\sum_{k=0}^{532-1} k = 532(532-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_532 : ∑ k ∈ range 532, k = 141246 := by sorry

end FiniteTriangular
