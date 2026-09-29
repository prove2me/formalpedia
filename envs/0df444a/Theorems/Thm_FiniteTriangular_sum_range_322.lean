-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_322
-- name    : FiniteTriangular.sum_range_322
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:19.512954+00:00
-- url     : https://prove2.me/theorems/08350dce-8f6f-4cba-9bb0-9877664f8dc5
-- title:
--   Sum of integers below 322
-- statement:
--   The sum of the nonnegative integers strictly less than $322$ equals $51681$. Equivalently, $\\sum_{k=0}^{322-1} k = 322(322-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_322 : ∑ k ∈ range 322, k = 51681 := by sorry

end FiniteTriangular
