-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_913
-- name    : FiniteTriangular.sum_range_913
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:51:46.124429+00:00
-- url     : https://prove2.me/theorems/65b54565-e8d7-4580-96cf-1373641910f0
-- title:
--   Sum of integers below 913
-- statement:
--   The sum of the nonnegative integers strictly less than $913$ equals $416328$. Equivalently, $\\sum_{k=0}^{913-1} k = 913(913-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_913 : ∑ k ∈ range 913, k = 416328 := by sorry

end FiniteTriangular
