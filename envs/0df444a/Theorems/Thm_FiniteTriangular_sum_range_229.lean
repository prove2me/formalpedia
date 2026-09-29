-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_229
-- name    : FiniteTriangular.sum_range_229
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:03.941442+00:00
-- url     : https://prove2.me/theorems/aca4e73e-52db-48bd-9595-8264671d367b
-- title:
--   Sum of integers below 229
-- statement:
--   The sum of the nonnegative integers strictly less than $229$ equals $26106$. Equivalently, $\\sum_{k=0}^{229-1} k = 229(229-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_229 : ∑ k ∈ range 229, k = 26106 := by sorry

end FiniteTriangular
