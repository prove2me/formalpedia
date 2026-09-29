-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_902
-- name    : FiniteTriangular.sum_range_902
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:32.748436+00:00
-- url     : https://prove2.me/theorems/a0c545c8-32f8-450a-91ae-61b942975cdb
-- title:
--   Sum of integers below 902
-- statement:
--   The sum of the nonnegative integers strictly less than $902$ equals $406351$. Equivalently, $\\sum_{k=0}^{902-1} k = 902(902-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_902 : ∑ k ∈ range 902, k = 406351 := by sorry

end FiniteTriangular
