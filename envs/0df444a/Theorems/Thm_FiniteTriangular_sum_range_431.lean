-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_431
-- name    : FiniteTriangular.sum_range_431
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:40.680661+00:00
-- url     : https://prove2.me/theorems/58d40dcc-d3bc-4430-845c-84823606cfde
-- title:
--   Sum of integers below 431
-- statement:
--   The sum of the nonnegative integers strictly less than $431$ equals $92665$. Equivalently, $\\sum_{k=0}^{431-1} k = 431(431-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_431 : ∑ k ∈ range 431, k = 92665 := by sorry

end FiniteTriangular
