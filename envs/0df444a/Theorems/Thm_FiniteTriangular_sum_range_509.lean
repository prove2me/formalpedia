-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_509
-- name    : FiniteTriangular.sum_range_509
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:12.986503+00:00
-- url     : https://prove2.me/theorems/34355447-1ce9-4393-afaf-d098422ac4bd
-- title:
--   Sum of integers below 509
-- statement:
--   The sum of the nonnegative integers strictly less than $509$ equals $129286$. Equivalently, $\\sum_{k=0}^{509-1} k = 509(509-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_509 : ∑ k ∈ range 509, k = 129286 := by sorry

end FiniteTriangular
