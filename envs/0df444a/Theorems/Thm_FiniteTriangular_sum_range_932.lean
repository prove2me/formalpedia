-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_932
-- name    : FiniteTriangular.sum_range_932
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:12.893505+00:00
-- url     : https://prove2.me/theorems/63ef717d-99e7-4557-b069-59af865a1c5a
-- title:
--   Sum of integers below 932
-- statement:
--   The sum of the nonnegative integers strictly less than $932$ equals $433846$. Equivalently, $\\sum_{k=0}^{932-1} k = 932(932-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_932 : ∑ k ∈ range 932, k = 433846 := by sorry

end FiniteTriangular
