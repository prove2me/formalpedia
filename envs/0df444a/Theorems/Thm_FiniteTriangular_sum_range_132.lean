-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_132
-- name    : FiniteTriangular.sum_range_132
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:51.239152+00:00
-- url     : https://prove2.me/theorems/8c2909fd-88cd-42c7-848e-eec1e08ec4fe
-- title:
--   Sum of integers below 132
-- statement:
--   The sum of the nonnegative integers strictly less than $132$ equals $8646$. Equivalently, $\sum_{k=0}^{132-1} k = 132(132-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_132 : ∑ k ∈ range 132, k = 8646 := by sorry

end FiniteTriangular
