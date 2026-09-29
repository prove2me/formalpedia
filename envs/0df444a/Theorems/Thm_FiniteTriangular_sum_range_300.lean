-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_300
-- name    : FiniteTriangular.sum_range_300
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:53.361727+00:00
-- url     : https://prove2.me/theorems/ee37a3bd-94c9-40c4-95f4-8df9c297affe
-- title:
--   Sum of integers below 300
-- statement:
--   The sum of the nonnegative integers strictly less than $300$ equals $44850$. Equivalently, $\\sum_{k=0}^{300-1} k = 300(300-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_300 : ∑ k ∈ range 300, k = 44850 := by sorry

end FiniteTriangular
