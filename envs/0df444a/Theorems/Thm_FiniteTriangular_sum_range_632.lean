-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_632
-- name    : FiniteTriangular.sum_range_632
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:49:53.201293+00:00
-- url     : https://prove2.me/theorems/13fe76c5-3d78-4edc-9016-d12629550acf
-- title:
--   Sum of integers below 632
-- statement:
--   The sum of the nonnegative integers strictly less than $632$ equals $199396$. Equivalently, $\\sum_{k=0}^{632-1} k = 632(632-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_632 : ∑ k ∈ range 632, k = 199396 := by sorry

end FiniteTriangular
