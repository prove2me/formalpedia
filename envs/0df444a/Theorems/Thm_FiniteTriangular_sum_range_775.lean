-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_775
-- name    : FiniteTriangular.sum_range_775
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:31.701299+00:00
-- url     : https://prove2.me/theorems/acf82505-9fa3-4385-9b83-06bf72a612e4
-- title:
--   Sum of integers below 775
-- statement:
--   The sum of the nonnegative integers strictly less than $775$ equals $299925$. Equivalently, $\\sum_{k=0}^{775-1} k = 775(775-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_775 : ∑ k ∈ range 775, k = 299925 := by sorry

end FiniteTriangular
