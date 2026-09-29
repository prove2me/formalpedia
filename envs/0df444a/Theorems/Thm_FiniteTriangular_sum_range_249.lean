-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_249
-- name    : FiniteTriangular.sum_range_249
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:09:01.933767+00:00
-- url     : https://prove2.me/theorems/01cf7cb1-a879-4590-a86d-65f2344b86ad
-- title:
--   Sum of integers below 249
-- statement:
--   The sum of the nonnegative integers strictly less than $249$ equals $30876$. Equivalently, $\\sum_{k=0}^{249-1} k = 249(249-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_249 : ∑ k ∈ range 249, k = 30876 := by sorry

end FiniteTriangular
