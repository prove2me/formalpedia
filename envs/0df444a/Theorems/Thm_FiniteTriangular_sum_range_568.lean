-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_568
-- name    : FiniteTriangular.sum_range_568
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:06.749859+00:00
-- url     : https://prove2.me/theorems/a6e493c4-bd0c-46ca-b8ff-6dc265324ae9
-- title:
--   Sum of integers below 568
-- statement:
--   The sum of the nonnegative integers strictly less than $568$ equals $161028$. Equivalently, $\\sum_{k=0}^{568-1} k = 568(568-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_568 : ∑ k ∈ range 568, k = 161028 := by sorry

end FiniteTriangular
