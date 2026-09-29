-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_125
-- name    : FiniteTriangular.sum_range_125
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:09.113438+00:00
-- url     : https://prove2.me/theorems/74c276e3-1b6e-4549-9314-6140885f31e5
-- title:
--   Sum of integers below 125
-- statement:
--   The sum of the nonnegative integers strictly less than $125$ equals $7750$. Equivalently, $\sum_{k=0}^{125-1} k = 125(125-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_125 : ∑ k ∈ range 125, k = 7750 := by sorry

end FiniteTriangular
