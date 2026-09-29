-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_881
-- name    : FiniteTriangular.sum_range_881
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:08.489519+00:00
-- url     : https://prove2.me/theorems/397cc8c7-bf06-414d-af61-7bb41018ded4
-- title:
--   Sum of integers below 881
-- statement:
--   The sum of the nonnegative integers strictly less than $881$ equals $387640$. Equivalently, $\\sum_{k=0}^{881-1} k = 881(881-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_881 : ∑ k ∈ range 881, k = 387640 := by sorry

end FiniteTriangular
