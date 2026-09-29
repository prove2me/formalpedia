-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_494
-- name    : FiniteTriangular.sum_range_494
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:46.724685+00:00
-- url     : https://prove2.me/theorems/ce8f4b93-6ab3-4bc8-b281-dd5c234ca751
-- title:
--   Sum of integers below 494
-- statement:
--   The sum of the nonnegative integers strictly less than $494$ equals $121771$. Equivalently, $\\sum_{k=0}^{494-1} k = 494(494-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_494 : ∑ k ∈ range 494, k = 121771 := by sorry

end FiniteTriangular
