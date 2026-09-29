-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_970
-- name    : FiniteTriangular.sum_range_970
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:15.381512+00:00
-- url     : https://prove2.me/theorems/dec19b4b-6aa7-44aa-8cd4-d121585fb308
-- title:
--   Sum of integers below 970
-- statement:
--   The sum of the nonnegative integers strictly less than $970$ equals $469965$. Equivalently, $\\sum_{k=0}^{970-1} k = 970(970-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_970 : ∑ k ∈ range 970, k = 469965 := by sorry

end FiniteTriangular
