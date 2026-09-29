-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_644
-- name    : FiniteTriangular.sum_range_644
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:12.878571+00:00
-- url     : https://prove2.me/theorems/c3b08ac4-864c-4ec2-b0a0-17ce117b301b
-- title:
--   Sum of integers below 644
-- statement:
--   The sum of the nonnegative integers strictly less than $644$ equals $207046$. Equivalently, $\\sum_{k=0}^{644-1} k = 644(644-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_644 : ∑ k ∈ range 644, k = 207046 := by sorry

end FiniteTriangular
