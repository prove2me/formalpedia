-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_280
-- name    : FiniteTriangular.sum_range_280
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:14:44.076257+00:00
-- url     : https://prove2.me/theorems/3b2f3667-1fda-4253-96ad-4d9b26e0ae69
-- title:
--   Sum of integers below 280
-- statement:
--   The sum of the nonnegative integers strictly less than $280$ equals $39060$. Equivalently, $\\sum_{k=0}^{280-1} k = 280(280-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_280 : ∑ k ∈ range 280, k = 39060 := by sorry

end FiniteTriangular
