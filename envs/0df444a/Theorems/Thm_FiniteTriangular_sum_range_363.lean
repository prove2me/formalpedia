-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_363
-- name    : FiniteTriangular.sum_range_363
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:11.358225+00:00
-- url     : https://prove2.me/theorems/1f893515-7553-4457-87f4-ceecdb290a20
-- title:
--   Sum of integers below 363
-- statement:
--   The sum of the nonnegative integers strictly less than $363$ equals $65703$. Equivalently, $\\sum_{k=0}^{363-1} k = 363(363-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_363 : ∑ k ∈ range 363, k = 65703 := by sorry

end FiniteTriangular
