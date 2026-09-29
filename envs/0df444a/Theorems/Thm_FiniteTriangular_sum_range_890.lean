-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_890
-- name    : FiniteTriangular.sum_range_890
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:55.611951+00:00
-- url     : https://prove2.me/theorems/8f35dc62-b425-48ed-a8fa-ec7a8a76aa53
-- title:
--   Sum of integers below 890
-- statement:
--   The sum of the nonnegative integers strictly less than $890$ equals $395605$. Equivalently, $\\sum_{k=0}^{890-1} k = 890(890-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_890 : ∑ k ∈ range 890, k = 395605 := by sorry

end FiniteTriangular
