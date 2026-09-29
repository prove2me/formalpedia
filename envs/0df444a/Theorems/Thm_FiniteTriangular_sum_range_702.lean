-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_702
-- name    : FiniteTriangular.sum_range_702
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:05:00.389751+00:00
-- url     : https://prove2.me/theorems/51d052aa-f01b-4e83-be63-697654b9dd7a
-- title:
--   Sum of integers below 702
-- statement:
--   The sum of the nonnegative integers strictly less than $702$ equals $246051$. Equivalently, $\\sum_{k=0}^{702-1} k = 702(702-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_702 : ∑ k ∈ range 702, k = 246051 := by sorry

end FiniteTriangular
