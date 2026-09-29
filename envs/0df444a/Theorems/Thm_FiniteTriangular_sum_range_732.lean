-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_732
-- name    : FiniteTriangular.sum_range_732
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:32.472617+00:00
-- url     : https://prove2.me/theorems/b4b15c5b-cb5b-473f-b797-5735ab74b510
-- title:
--   Sum of integers below 732
-- statement:
--   The sum of the nonnegative integers strictly less than $732$ equals $267546$. Equivalently, $\\sum_{k=0}^{732-1} k = 732(732-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_732 : ∑ k ∈ range 732, k = 267546 := by sorry

end FiniteTriangular
