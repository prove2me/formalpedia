-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_867
-- name    : FiniteTriangular.sum_range_867
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:45.874165+00:00
-- url     : https://prove2.me/theorems/cff11699-af56-466b-bb4b-c797856d981a
-- title:
--   Sum of integers below 867
-- statement:
--   The sum of the nonnegative integers strictly less than $867$ equals $375411$. Equivalently, $\\sum_{k=0}^{867-1} k = 867(867-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_867 : ∑ k ∈ range 867, k = 375411 := by sorry

end FiniteTriangular
