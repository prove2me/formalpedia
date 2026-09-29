-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_559
-- name    : FiniteTriangular.sum_range_559
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:17.246572+00:00
-- url     : https://prove2.me/theorems/a7482fbf-ae03-4b9a-83e8-1a32a91aefd8
-- title:
--   Sum of integers below 559
-- statement:
--   The sum of the nonnegative integers strictly less than $559$ equals $155961$. Equivalently, $\\sum_{k=0}^{559-1} k = 559(559-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_559 : ∑ k ∈ range 559, k = 155961 := by sorry

end FiniteTriangular
