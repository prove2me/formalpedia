-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_789
-- name    : FiniteTriangular.sum_range_789
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:56.098859+00:00
-- url     : https://prove2.me/theorems/1f4a61df-ab87-489d-b150-83c4f41c1c13
-- title:
--   Sum of integers below 789
-- statement:
--   The sum of the nonnegative integers strictly less than $789$ equals $310866$. Equivalently, $\\sum_{k=0}^{789-1} k = 789(789-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_789 : ∑ k ∈ range 789, k = 310866 := by sorry

end FiniteTriangular
