-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_150
-- name    : FiniteTriangular.sum_range_150
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:15.818454+00:00
-- url     : https://prove2.me/theorems/b188fbe2-8e8b-4672-a4e8-21795a56a619
-- title:
--   Sum of integers below 150
-- statement:
--   The sum of the nonnegative integers strictly less than $150$ equals $11175$. Equivalently, $\sum_{k=0}^{150-1} k = 150(150-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_150 : ∑ k ∈ range 150, k = 11175 := by sorry

end FiniteTriangular
