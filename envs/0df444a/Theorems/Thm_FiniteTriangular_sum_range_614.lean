-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_614
-- name    : FiniteTriangular.sum_range_614
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:33.233748+00:00
-- url     : https://prove2.me/theorems/00f96713-13b1-4b22-ba37-a9a195fc0c45
-- title:
--   Sum of integers below 614
-- statement:
--   The sum of the nonnegative integers strictly less than $614$ equals $188191$. Equivalently, $\\sum_{k=0}^{614-1} k = 614(614-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_614 : ∑ k ∈ range 614, k = 188191 := by sorry

end FiniteTriangular
