-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_514
-- name    : FiniteTriangular.sum_range_514
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:52.569853+00:00
-- url     : https://prove2.me/theorems/c1c445a8-e932-4e01-970b-be4f59f596e6
-- title:
--   Sum of integers below 514
-- statement:
--   The sum of the nonnegative integers strictly less than $514$ equals $131841$. Equivalently, $\\sum_{k=0}^{514-1} k = 514(514-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_514 : ∑ k ∈ range 514, k = 131841 := by sorry

end FiniteTriangular
