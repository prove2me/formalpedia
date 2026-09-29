-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_898
-- name    : FiniteTriangular.sum_range_898
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:32.228504+00:00
-- url     : https://prove2.me/theorems/37e21799-7b6b-4988-b92f-e67198eb4959
-- title:
--   Sum of integers below 898
-- statement:
--   The sum of the nonnegative integers strictly less than $898$ equals $402753$. Equivalently, $\\sum_{k=0}^{898-1} k = 898(898-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_898 : ∑ k ∈ range 898, k = 402753 := by sorry

end FiniteTriangular
