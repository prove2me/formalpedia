-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_872
-- name    : FiniteTriangular.sum_range_872
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:46.816736+00:00
-- url     : https://prove2.me/theorems/d18ef933-8884-4363-864e-cfb5e5129724
-- title:
--   Sum of integers below 872
-- statement:
--   The sum of the nonnegative integers strictly less than $872$ equals $379756$. Equivalently, $\\sum_{k=0}^{872-1} k = 872(872-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_872 : ∑ k ∈ range 872, k = 379756 := by sorry

end FiniteTriangular
