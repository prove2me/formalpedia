-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_102
-- name    : FiniteTriangular.sum_range_102
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:24.186436+00:00
-- url     : https://prove2.me/theorems/6c27eb99-6c86-4783-9d93-fb3e0dce9bf4
-- title:
--   Sum of integers below 102
-- statement:
--   The sum of the nonnegative integers strictly less than $102$ equals $5151$. Equivalently, $\sum_{k=0}^{102-1} k = 102(102-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_102 : ∑ k ∈ range 102, k = 5151 := by sorry

end FiniteTriangular
