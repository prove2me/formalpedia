-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_407
-- name    : FiniteTriangular.sum_range_407
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:22.929785+00:00
-- url     : https://prove2.me/theorems/5a6dadff-d87e-445d-8380-8991a08f7c51
-- title:
--   Sum of integers below 407
-- statement:
--   The sum of the nonnegative integers strictly less than $407$ equals $82621$. Equivalently, $\\sum_{k=0}^{407-1} k = 407(407-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_407 : ∑ k ∈ range 407, k = 82621 := by sorry

end FiniteTriangular
