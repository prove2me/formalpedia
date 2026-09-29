-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_391
-- name    : FiniteTriangular.sum_range_391
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:46:56.294342+00:00
-- url     : https://prove2.me/theorems/206c48fb-9e24-4e07-a766-5c12de851530
-- title:
--   Sum of integers below 391
-- statement:
--   The sum of the nonnegative integers strictly less than $391$ equals $76245$. Equivalently, $\\sum_{k=0}^{391-1} k = 391(391-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_391 : ∑ k ∈ range 391, k = 76245 := by sorry

end FiniteTriangular
