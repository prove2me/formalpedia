-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_613
-- name    : FiniteTriangular.sum_range_613
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:28.886352+00:00
-- url     : https://prove2.me/theorems/4f4ca072-a869-42b3-86a0-51c222ed6026
-- title:
--   Sum of integers below 613
-- statement:
--   The sum of the nonnegative integers strictly less than $613$ equals $187578$. Equivalently, $\\sum_{k=0}^{613-1} k = 613(613-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_613 : ∑ k ∈ range 613, k = 187578 := by sorry

end FiniteTriangular
