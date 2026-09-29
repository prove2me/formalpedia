-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_759
-- name    : FiniteTriangular.sum_range_759
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:17:57.921037+00:00
-- url     : https://prove2.me/theorems/7cf0490d-c718-486c-8093-7528daef5914
-- title:
--   Sum of integers below 759
-- statement:
--   The sum of the nonnegative integers strictly less than $759$ equals $287661$. Equivalently, $\\sum_{k=0}^{759-1} k = 759(759-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_759 : ∑ k ∈ range 759, k = 287661 := by sorry

end FiniteTriangular
