-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_699
-- name    : FiniteTriangular.sum_range_699
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:04:57.792847+00:00
-- url     : https://prove2.me/theorems/1287b25d-c97d-4ac3-ba93-8ab6ade635f9
-- title:
--   Sum of integers below 699
-- statement:
--   The sum of the nonnegative integers strictly less than $699$ equals $243951$. Equivalently, $\\sum_{k=0}^{699-1} k = 699(699-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_699 : ∑ k ∈ range 699, k = 243951 := by sorry

end FiniteTriangular
