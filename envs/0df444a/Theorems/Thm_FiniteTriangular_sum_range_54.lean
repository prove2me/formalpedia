-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_54
-- name    : FiniteTriangular.sum_range_54
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:18:59.752648+00:00
-- url     : https://prove2.me/theorems/469620d9-21be-4d19-96c0-8b04ad34b054
-- title:
--   Sum of integers below 54
-- statement:
--   The sum of the nonnegative integers strictly less than $54$ equals $1431$. Equivalently, $\sum_{k=0}^{54-1} k = 54(54-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_54 : ∑ k ∈ range 54, k = 1431 := by sorry

end FiniteTriangular
