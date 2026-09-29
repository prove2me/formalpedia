-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_35
-- name    : FiniteTriangular.sum_range_35
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:53.167895+00:00
-- url     : https://prove2.me/theorems/fc938479-5c25-45e4-ad26-627997fa2e00
-- title:
--   Sum of integers below 35
-- statement:
--   The sum of the nonnegative integers strictly less than $35$ equals $595$. Equivalently, $\sum_{k=0}^{35-1} k = 35(35-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_35 : ∑ k ∈ range 35, k = 595 := by sorry

end FiniteTriangular
