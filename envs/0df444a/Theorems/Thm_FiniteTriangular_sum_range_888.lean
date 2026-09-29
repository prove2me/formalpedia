-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_888
-- name    : FiniteTriangular.sum_range_888
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:09.993206+00:00
-- url     : https://prove2.me/theorems/9ddf0b86-874b-4826-9962-3fea1f630ef0
-- title:
--   Sum of integers below 888
-- statement:
--   The sum of the nonnegative integers strictly less than $888$ equals $393828$. Equivalently, $\\sum_{k=0}^{888-1} k = 888(888-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_888 : ∑ k ∈ range 888, k = 393828 := by sorry

end FiniteTriangular
