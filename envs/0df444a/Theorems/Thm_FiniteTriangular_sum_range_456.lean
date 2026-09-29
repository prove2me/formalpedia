-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_456
-- name    : FiniteTriangular.sum_range_456
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:53.260615+00:00
-- url     : https://prove2.me/theorems/baeb7429-5caa-4fe1-a178-d29eb27962f9
-- title:
--   Sum of integers below 456
-- statement:
--   The sum of the nonnegative integers strictly less than $456$ equals $103740$. Equivalently, $\\sum_{k=0}^{456-1} k = 456(456-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_456 : ∑ k ∈ range 456, k = 103740 := by sorry

end FiniteTriangular
