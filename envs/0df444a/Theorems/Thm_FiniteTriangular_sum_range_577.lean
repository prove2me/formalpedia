-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_577
-- name    : FiniteTriangular.sum_range_577
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:35.320415+00:00
-- url     : https://prove2.me/theorems/171002f7-88e5-4dbe-8e34-1a195faeaf6f
-- title:
--   Sum of integers below 577
-- statement:
--   The sum of the nonnegative integers strictly less than $577$ equals $166176$. Equivalently, $\\sum_{k=0}^{577-1} k = 577(577-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_577 : ∑ k ∈ range 577, k = 166176 := by sorry

end FiniteTriangular
