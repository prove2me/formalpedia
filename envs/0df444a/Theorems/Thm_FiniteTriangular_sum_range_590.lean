-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_590
-- name    : FiniteTriangular.sum_range_590
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:41:24.168982+00:00
-- url     : https://prove2.me/theorems/8997837e-d44a-4abe-b388-bda3ab99fd96
-- title:
--   Sum of integers below 590
-- statement:
--   The sum of the nonnegative integers strictly less than $590$ equals $173755$. Equivalently, $\\sum_{k=0}^{590-1} k = 590(590-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_590 : ∑ k ∈ range 590, k = 173755 := by sorry

end FiniteTriangular
