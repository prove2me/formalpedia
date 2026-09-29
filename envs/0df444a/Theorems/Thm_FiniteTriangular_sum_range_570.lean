-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_570
-- name    : FiniteTriangular.sum_range_570
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:43.294762+00:00
-- url     : https://prove2.me/theorems/96f45cab-7126-477e-aa6c-a3b194699a16
-- title:
--   Sum of integers below 570
-- statement:
--   The sum of the nonnegative integers strictly less than $570$ equals $162165$. Equivalently, $\\sum_{k=0}^{570-1} k = 570(570-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_570 : ∑ k ∈ range 570, k = 162165 := by sorry

end FiniteTriangular
