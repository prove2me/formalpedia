-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_531
-- name    : FiniteTriangular.sum_range_531
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:17.410764+00:00
-- url     : https://prove2.me/theorems/2859717c-ae19-4dfe-a138-aa9d63559cf6
-- title:
--   Sum of integers below 531
-- statement:
--   The sum of the nonnegative integers strictly less than $531$ equals $140715$. Equivalently, $\\sum_{k=0}^{531-1} k = 531(531-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_531 : ∑ k ∈ range 531, k = 140715 := by sorry

end FiniteTriangular
