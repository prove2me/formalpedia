-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_545
-- name    : FiniteTriangular.sum_range_545
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:30:44.202167+00:00
-- url     : https://prove2.me/theorems/1c4805bb-76d8-4afa-87df-86f6095b5747
-- title:
--   Sum of integers below 545
-- statement:
--   The sum of the nonnegative integers strictly less than $545$ equals $148240$. Equivalently, $\\sum_{k=0}^{545-1} k = 545(545-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_545 : ∑ k ∈ range 545, k = 148240 := by sorry

end FiniteTriangular
