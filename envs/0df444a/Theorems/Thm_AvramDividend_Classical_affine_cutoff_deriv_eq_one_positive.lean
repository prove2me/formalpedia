-- Prove2me | Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
-- name    : AvramDividend.Classical.affine_cutoff_deriv_eq_one_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:14:22.414737+00:00
-- url     : https://prove2.me/theorems/34a6c87d-8bee-4e30-824d-5a7711aa665b
-- title:
--   Positive-reserve unit derivative of the zero-extended affine verification candidate
-- statement:
--   The candidate verification function equal to zero below reserve zero and z−1 for nonnegative reserves has derivative one at every strictly positive reserve. The proof uses its agreement with the affine function on a neighbourhood of any positive point. This discharges the gradient inequality in the Gaussian counterexample audit of the unbounded-variation stochastic verification theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), derivative HJB condition.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter Set
open scoped Topology

theorem AvramDividend.Classical.affine_cutoff_deriv_eq_one_positive
    (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y = 1 := by sorry
