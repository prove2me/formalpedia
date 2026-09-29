-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_958
-- name    : FiniteTriangular.sum_range_958
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:48.178573+00:00
-- url     : https://prove2.me/theorems/4d01eab3-7401-444d-85e5-56021f1e7871
-- title:
--   Sum of integers below 958
-- statement:
--   The sum of the nonnegative integers strictly less than $958$ equals $458403$. Equivalently, $\\sum_{k=0}^{958-1} k = 958(958-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_958 : ∑ k ∈ range 958, k = 458403 := by sorry

end FiniteTriangular
