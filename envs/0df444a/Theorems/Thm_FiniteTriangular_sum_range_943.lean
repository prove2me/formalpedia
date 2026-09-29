-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_943
-- name    : FiniteTriangular.sum_range_943
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:56:59.749002+00:00
-- url     : https://prove2.me/theorems/94ff7140-1437-4b0d-976d-55fa18e0e9af
-- title:
--   Sum of integers below 943
-- statement:
--   The sum of the nonnegative integers strictly less than $943$ equals $444153$. Equivalently, $\\sum_{k=0}^{943-1} k = 943(943-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_943 : ∑ k ∈ range 943, k = 444153 := by sorry

end FiniteTriangular
