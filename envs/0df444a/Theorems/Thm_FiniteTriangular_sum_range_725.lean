-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_725
-- name    : FiniteTriangular.sum_range_725
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:46.892359+00:00
-- url     : https://prove2.me/theorems/5627a8f1-7fe5-404e-9f58-11ed75974a42
-- title:
--   Sum of integers below 725
-- statement:
--   The sum of the nonnegative integers strictly less than $725$ equals $262450$. Equivalently, $\\sum_{k=0}^{725-1} k = 725(725-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_725 : ∑ k ∈ range 725, k = 262450 := by sorry

end FiniteTriangular
