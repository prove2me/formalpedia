-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_421
-- name    : FiniteTriangular.sum_range_421
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:52.816549+00:00
-- url     : https://prove2.me/theorems/96a64ec1-ea28-4b60-9d13-df455939c28b
-- title:
--   Sum of integers below 421
-- statement:
--   The sum of the nonnegative integers strictly less than $421$ equals $88410$. Equivalently, $\\sum_{k=0}^{421-1} k = 421(421-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_421 : ∑ k ∈ range 421, k = 88410 := by sorry

end FiniteTriangular
