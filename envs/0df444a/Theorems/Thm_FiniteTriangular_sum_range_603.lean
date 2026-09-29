-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_603
-- name    : FiniteTriangular.sum_range_603
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:44.994672+00:00
-- url     : https://prove2.me/theorems/770acf30-a60d-4246-b9e3-912ec2c732e2
-- title:
--   Sum of integers below 603
-- statement:
--   The sum of the nonnegative integers strictly less than $603$ equals $181503$. Equivalently, $\\sum_{k=0}^{603-1} k = 603(603-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_603 : ∑ k ∈ range 603, k = 181503 := by sorry

end FiniteTriangular
