-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_753
-- name    : FiniteTriangular.sum_range_753
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:58.189673+00:00
-- url     : https://prove2.me/theorems/a73fb759-2755-4ec0-a7ca-d14458c7b1ca
-- title:
--   Sum of integers below 753
-- statement:
--   The sum of the nonnegative integers strictly less than $753$ equals $283128$. Equivalently, $\\sum_{k=0}^{753-1} k = 753(753-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_753 : ∑ k ∈ range 753, k = 283128 := by sorry

end FiniteTriangular
