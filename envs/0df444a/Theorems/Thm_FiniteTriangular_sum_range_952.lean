-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_952
-- name    : FiniteTriangular.sum_range_952
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:56.129507+00:00
-- url     : https://prove2.me/theorems/477adbd0-f78c-45d5-bc92-15b4cea33976
-- title:
--   Sum of integers below 952
-- statement:
--   The sum of the nonnegative integers strictly less than $952$ equals $452676$. Equivalently, $\\sum_{k=0}^{952-1} k = 952(952-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_952 : ∑ k ∈ range 952, k = 452676 := by sorry

end FiniteTriangular
