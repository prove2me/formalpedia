-- Prove2me | Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive
-- name    : AvramDividend.Classical.affine_cutoff_continuous_nonnegative_smooth_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:24:33.119571+00:00
-- url     : https://prove2.me/theorems/39391b63-6067-46a6-8d41-4e2498646a0c
-- title:
--   Zero-extended affine verification candidate is continuous on nonnegative reserves and C² on positive reserves
-- statement:
--   The payoff function w(z)=0 for negative z and z−1 otherwise coincides on nonnegative reserves with the affine function z−1, and is consequently continuous there. It also coincides with the affine function on positive reserves, making it C² there. These are the regularity hypotheses for the proposed Gaussian process audit of the unbounded-variation verification theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), candidate verification regularity.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Set

theorem AvramDividend.Classical.affine_cutoff_continuous_nonnegative_smooth_positive :
    ContinuousOn (fun z : ℝ => if z < 0 then 0 else z - 1) (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1) (Ioi (0 : ℝ)) := by sorry
