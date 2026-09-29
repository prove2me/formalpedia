-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_457
-- name    : FiniteTriangular.sum_range_457
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:48.47399+00:00
-- url     : https://prove2.me/theorems/40dd06f1-5ae9-4362-b073-0500f8eae97c
-- title:
--   Sum of integers below 457
-- statement:
--   The sum of the nonnegative integers strictly less than $457$ equals $104196$. Equivalently, $\\sum_{k=0}^{457-1} k = 457(457-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_457 : ∑ k ∈ range 457, k = 104196 := by sorry

end FiniteTriangular
