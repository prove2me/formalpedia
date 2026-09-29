-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_830
-- name    : FiniteTriangular.sum_range_830
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:30.897512+00:00
-- url     : https://prove2.me/theorems/4c3c7b4f-a2bc-4141-848b-1c2435352c4f
-- title:
--   Sum of integers below 830
-- statement:
--   The sum of the nonnegative integers strictly less than $830$ equals $344035$. Equivalently, $\\sum_{k=0}^{830-1} k = 830(830-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_830 : ∑ k ∈ range 830, k = 344035 := by sorry

end FiniteTriangular
