-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_672
-- name    : FiniteTriangular.sum_range_672
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:14.156113+00:00
-- url     : https://prove2.me/theorems/cdcf0b15-1b62-477b-afea-1502f5d99786
-- title:
--   Sum of integers below 672
-- statement:
--   The sum of the nonnegative integers strictly less than $672$ equals $225456$. Equivalently, $\\sum_{k=0}^{672-1} k = 672(672-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_672 : ∑ k ∈ range 672, k = 225456 := by sorry

end FiniteTriangular
