-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_891
-- name    : FiniteTriangular.sum_range_891
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:46:55.233624+00:00
-- url     : https://prove2.me/theorems/5e9c8e7f-dc65-48de-ad1e-d099c2f012af
-- title:
--   Sum of integers below 891
-- statement:
--   The sum of the nonnegative integers strictly less than $891$ equals $396495$. Equivalently, $\\sum_{k=0}^{891-1} k = 891(891-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_891 : ∑ k ∈ range 891, k = 396495 := by sorry

end FiniteTriangular
