-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_674
-- name    : FiniteTriangular.sum_range_674
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:58.933542+00:00
-- url     : https://prove2.me/theorems/139cba30-9978-44fc-9dcc-b87ae51b0c54
-- title:
--   Sum of integers below 674
-- statement:
--   The sum of the nonnegative integers strictly less than $674$ equals $226801$. Equivalently, $\\sum_{k=0}^{674-1} k = 674(674-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_674 : ∑ k ∈ range 674, k = 226801 := by sorry

end FiniteTriangular
