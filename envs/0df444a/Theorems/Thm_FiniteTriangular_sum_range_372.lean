-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_372
-- name    : FiniteTriangular.sum_range_372
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:06.312506+00:00
-- url     : https://prove2.me/theorems/e5e1054a-f654-43ae-97be-d07ab74562cf
-- title:
--   Sum of integers below 372
-- statement:
--   The sum of the nonnegative integers strictly less than $372$ equals $69006$. Equivalently, $\\sum_{k=0}^{372-1} k = 372(372-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_372 : ∑ k ∈ range 372, k = 69006 := by sorry

end FiniteTriangular
