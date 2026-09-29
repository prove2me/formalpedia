-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_658
-- name    : FiniteTriangular.sum_range_658
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:36.122205+00:00
-- url     : https://prove2.me/theorems/360ea744-592e-4b2f-88bf-632a109a204e
-- title:
--   Sum of integers below 658
-- statement:
--   The sum of the nonnegative integers strictly less than $658$ equals $216153$. Equivalently, $\\sum_{k=0}^{658-1} k = 658(658-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_658 : ∑ k ∈ range 658, k = 216153 := by sorry

end FiniteTriangular
