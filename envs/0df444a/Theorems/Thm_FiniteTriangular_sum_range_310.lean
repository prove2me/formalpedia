-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_310
-- name    : FiniteTriangular.sum_range_310
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:53.756434+00:00
-- url     : https://prove2.me/theorems/9c274424-b605-41f9-ad73-fbd17e487667
-- title:
--   Sum of integers below 310
-- statement:
--   The sum of the nonnegative integers strictly less than $310$ equals $47895$. Equivalently, $\\sum_{k=0}^{310-1} k = 310(310-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_310 : ∑ k ∈ range 310, k = 47895 := by sorry

end FiniteTriangular
