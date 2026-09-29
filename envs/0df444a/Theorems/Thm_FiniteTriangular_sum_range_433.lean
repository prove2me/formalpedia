-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_433
-- name    : FiniteTriangular.sum_range_433
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:26.383148+00:00
-- url     : https://prove2.me/theorems/bc6affe2-7ba8-4740-808a-9632d29dbfaf
-- title:
--   Sum of integers below 433
-- statement:
--   The sum of the nonnegative integers strictly less than $433$ equals $93528$. Equivalently, $\\sum_{k=0}^{433-1} k = 433(433-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_433 : ∑ k ∈ range 433, k = 93528 := by sorry

end FiniteTriangular
