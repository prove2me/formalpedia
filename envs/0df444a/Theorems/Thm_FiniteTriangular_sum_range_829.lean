-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_829
-- name    : FiniteTriangular.sum_range_829
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:30.537859+00:00
-- url     : https://prove2.me/theorems/948a9db8-aaa3-461b-a616-398d5c2bf039
-- title:
--   Sum of integers below 829
-- statement:
--   The sum of the nonnegative integers strictly less than $829$ equals $343206$. Equivalently, $\\sum_{k=0}^{829-1} k = 829(829-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_829 : ∑ k ∈ range 829, k = 343206 := by sorry

end FiniteTriangular
