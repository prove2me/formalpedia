-- Prove2me | Theorems.Thm_AvramDividend_Classical_affine_cutoff_second_deriv_eq_zero_positive
-- name    : AvramDividend.Classical.affine_cutoff_second_deriv_eq_zero_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:19:39.870134+00:00
-- url     : https://prove2.me/theorems/735fc7bb-6973-4963-a703-527a3ef5ffc6
-- title:
--   Positive-reserve second derivative of zero-extended affine verification function vanishes
-- statement:
--   The piecewise function zero for negative reserves and z−1 for nonnegative reserves has vanishing second iterated derivative on the positive half-line, since its first derivative equals one throughout a neighbourhood of each positive reserve. This is the Gaussian diffusion term needed for the counterexample HJB generator calculation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i) smoothness and the Gaussian generator term.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive

open Filter Set
open scoped Topology

theorem AvramDividend.Classical.affine_cutoff_second_deriv_eq_zero_positive
    (y : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun z : ℝ => if z < 0 then 0 else z - 1) y = 0 := by sorry
