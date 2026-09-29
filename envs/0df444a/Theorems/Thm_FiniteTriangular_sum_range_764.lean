-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_764
-- name    : FiniteTriangular.sum_range_764
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:37.40561+00:00
-- url     : https://prove2.me/theorems/e6fb43ca-56b8-4434-b264-acf4363e5bba
-- title:
--   Sum of integers below 764
-- statement:
--   The sum of the nonnegative integers strictly less than $764$ equals $291466$. Equivalently, $\\sum_{k=0}^{764-1} k = 764(764-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_764 : ∑ k ∈ range 764, k = 291466 := by sorry

end FiniteTriangular
