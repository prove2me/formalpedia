-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_488
-- name    : FiniteTriangular.sum_range_488
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:10.171732+00:00
-- url     : https://prove2.me/theorems/b0a06d70-932d-427c-9388-45529fe0ef24
-- title:
--   Sum of integers below 488
-- statement:
--   The sum of the nonnegative integers strictly less than $488$ equals $118828$. Equivalently, $\\sum_{k=0}^{488-1} k = 488(488-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_488 : ∑ k ∈ range 488, k = 118828 := by sorry

end FiniteTriangular
