-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_71
-- name    : FiniteTriangular.sum_range_71
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:48.304584+00:00
-- url     : https://prove2.me/theorems/d6734e29-d060-464d-bf94-1fc74e3b2bac
-- title:
--   Sum of integers below 71
-- statement:
--   The sum of the nonnegative integers strictly less than $71$ equals $2485$. Equivalently, $\sum_{k=0}^{71-1} k = 71(71-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_71 : ∑ k ∈ range 71, k = 2485 := by sorry

end FiniteTriangular
