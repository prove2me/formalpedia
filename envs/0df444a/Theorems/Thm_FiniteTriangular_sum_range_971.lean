-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_971
-- name    : FiniteTriangular.sum_range_971
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:14.01643+00:00
-- url     : https://prove2.me/theorems/1bc108b4-7e35-431b-8a51-32ad53e5d9f9
-- title:
--   Sum of integers below 971
-- statement:
--   The sum of the nonnegative integers strictly less than $971$ equals $470935$. Equivalently, $\\sum_{k=0}^{971-1} k = 971(971-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_971 : ∑ k ∈ range 971, k = 470935 := by sorry

end FiniteTriangular
