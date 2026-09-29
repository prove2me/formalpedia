-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_878
-- name    : FiniteTriangular.sum_range_878
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:31.95437+00:00
-- url     : https://prove2.me/theorems/40aaaf21-cfdd-4b12-af59-91a07645ec8a
-- title:
--   Sum of integers below 878
-- statement:
--   The sum of the nonnegative integers strictly less than $878$ equals $385003$. Equivalently, $\\sum_{k=0}^{878-1} k = 878(878-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_878 : ∑ k ∈ range 878, k = 385003 := by sorry

end FiniteTriangular
