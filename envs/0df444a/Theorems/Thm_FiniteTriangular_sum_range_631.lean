-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_631
-- name    : FiniteTriangular.sum_range_631
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:52.920112+00:00
-- url     : https://prove2.me/theorems/ccfb3308-dc0d-4d58-be62-9266bfae4ce3
-- title:
--   Sum of integers below 631
-- statement:
--   The sum of the nonnegative integers strictly less than $631$ equals $198765$. Equivalently, $\\sum_{k=0}^{631-1} k = 631(631-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_631 : ∑ k ∈ range 631, k = 198765 := by sorry

end FiniteTriangular
