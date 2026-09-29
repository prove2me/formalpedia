-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_510
-- name    : FiniteTriangular.sum_range_510
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:09.440729+00:00
-- url     : https://prove2.me/theorems/13488a14-beb5-46bd-adac-68bb89164a3b
-- title:
--   Sum of integers below 510
-- statement:
--   The sum of the nonnegative integers strictly less than $510$ equals $129795$. Equivalently, $\\sum_{k=0}^{510-1} k = 510(510-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_510 : ∑ k ∈ range 510, k = 129795 := by sorry

end FiniteTriangular
