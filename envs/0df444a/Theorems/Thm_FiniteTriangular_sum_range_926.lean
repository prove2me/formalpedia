-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_926
-- name    : FiniteTriangular.sum_range_926
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:37.236271+00:00
-- url     : https://prove2.me/theorems/26f88800-8f27-4215-a9da-823eefc997f5
-- title:
--   Sum of integers below 926
-- statement:
--   The sum of the nonnegative integers strictly less than $926$ equals $428275$. Equivalently, $\\sum_{k=0}^{926-1} k = 926(926-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_926 : ∑ k ∈ range 926, k = 428275 := by sorry

end FiniteTriangular
