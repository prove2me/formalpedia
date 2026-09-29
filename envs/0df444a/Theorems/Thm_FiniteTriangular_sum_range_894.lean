-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_894
-- name    : FiniteTriangular.sum_range_894
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:55.117502+00:00
-- url     : https://prove2.me/theorems/53630cb3-505d-41a1-809e-fb979275e9fb
-- title:
--   Sum of integers below 894
-- statement:
--   The sum of the nonnegative integers strictly less than $894$ equals $399171$. Equivalently, $\\sum_{k=0}^{894-1} k = 894(894-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_894 : ∑ k ∈ range 894, k = 399171 := by sorry

end FiniteTriangular
