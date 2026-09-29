-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_721
-- name    : FiniteTriangular.sum_range_721
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:10:47.173986+00:00
-- url     : https://prove2.me/theorems/4d00de69-0d68-4d7e-9ec6-9534c6767ee5
-- title:
--   Sum of integers below 721
-- statement:
--   The sum of the nonnegative integers strictly less than $721$ equals $259560$. Equivalently, $\\sum_{k=0}^{721-1} k = 721(721-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_721 : ∑ k ∈ range 721, k = 259560 := by sorry

end FiniteTriangular
