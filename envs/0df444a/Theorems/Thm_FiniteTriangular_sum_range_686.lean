-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_686
-- name    : FiniteTriangular.sum_range_686
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:47.042415+00:00
-- url     : https://prove2.me/theorems/9ed13b70-9fa0-4560-afb8-a554cc8f392a
-- title:
--   Sum of integers below 686
-- statement:
--   The sum of the nonnegative integers strictly less than $686$ equals $234955$. Equivalently, $\\sum_{k=0}^{686-1} k = 686(686-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_686 : ∑ k ∈ range 686, k = 234955 := by sorry

end FiniteTriangular
