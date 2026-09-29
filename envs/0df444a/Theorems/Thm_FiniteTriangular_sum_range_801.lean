-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_801
-- name    : FiniteTriangular.sum_range_801
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:08.287526+00:00
-- url     : https://prove2.me/theorems/fd8aadf0-215a-4203-8591-4b42a78d6703
-- title:
--   Sum of integers below 801
-- statement:
--   The sum of the nonnegative integers strictly less than $801$ equals $320400$. Equivalently, $\\sum_{k=0}^{801-1} k = 801(801-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_801 : ∑ k ∈ range 801, k = 320400 := by sorry

end FiniteTriangular
