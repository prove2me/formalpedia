-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_717
-- name    : FiniteTriangular.sum_range_717
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:43.289785+00:00
-- url     : https://prove2.me/theorems/84ed5dcd-29ac-4d61-ad70-8fb358849887
-- title:
--   Sum of integers below 717
-- statement:
--   The sum of the nonnegative integers strictly less than $717$ equals $256686$. Equivalently, $\\sum_{k=0}^{717-1} k = 717(717-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_717 : ∑ k ∈ range 717, k = 256686 := by sorry

end FiniteTriangular
