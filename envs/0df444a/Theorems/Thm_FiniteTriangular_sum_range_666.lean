-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_666
-- name    : FiniteTriangular.sum_range_666
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:58:10.496619+00:00
-- url     : https://prove2.me/theorems/3472eb56-7dca-44b3-83ab-710f86f9fc62
-- title:
--   Sum of integers below 666
-- statement:
--   The sum of the nonnegative integers strictly less than $666$ equals $221445$. Equivalently, $\\sum_{k=0}^{666-1} k = 666(666-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_666 : ∑ k ∈ range 666, k = 221445 := by sorry

end FiniteTriangular
