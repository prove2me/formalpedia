-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_68
-- name    : FiniteTriangular.sum_range_68
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:56.685531+00:00
-- url     : https://prove2.me/theorems/d062e25e-7af6-458b-8602-f5015d670462
-- title:
--   Sum of integers below 68
-- statement:
--   The sum of the nonnegative integers strictly less than $68$ equals $2278$. Equivalently, $\sum_{k=0}^{68-1} k = 68(68-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_68 : ∑ k ∈ range 68, k = 2278 := by sorry

end FiniteTriangular
