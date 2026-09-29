-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_664
-- name    : FiniteTriangular.sum_range_664
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:35.999387+00:00
-- url     : https://prove2.me/theorems/22f38d35-3333-4975-a479-2fb7681a646c
-- title:
--   Sum of integers below 664
-- statement:
--   The sum of the nonnegative integers strictly less than $664$ equals $220116$. Equivalently, $\\sum_{k=0}^{664-1} k = 664(664-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_664 : ∑ k ∈ range 664, k = 220116 := by sorry

end FiniteTriangular
