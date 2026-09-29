-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_405
-- name    : FiniteTriangular.sum_range_405
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:19.048486+00:00
-- url     : https://prove2.me/theorems/7ed1b43c-3f40-4edb-ae47-43ea119d5c4d
-- title:
--   Sum of integers below 405
-- statement:
--   The sum of the nonnegative integers strictly less than $405$ equals $81810$. Equivalently, $\\sum_{k=0}^{405-1} k = 405(405-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_405 : ∑ k ∈ range 405, k = 81810 := by sorry

end FiniteTriangular
