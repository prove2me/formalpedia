-- Prove2me | Theorems.Thm_AvramDividend_Classical_recordPartition_Ioc_disjoint
-- name    : AvramDividend.Classical.recordPartition_Ioc_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:38:42.497726+00:00
-- url     : https://prove2.me/theorems/26b30a5d-eb69-4fbf-b1ab-aa17bfbb5d8e
-- title:
--   Ordered record-level half-open partition cells are pairwise disjoint
-- statement:
--   For a nondecreasing sequence of real record-level partition points, any two differently indexed half-open cells (u_i,u_(i+1)] and (u_j,u_(j+1)] with i<j are disjoint. Their strict-left and weak-right endpoints prevent counting a payment at a common endpoint twice. This is a deterministic measurable partition component needed for countable interval Stieltjes reward decompositions.
-- source:
--   Pinned Mathlib Set.disjoint_left from Mathlib.Data.Set.Disjoint and monotonicity of u. No stochastic assumptions.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.Set.Disjoint

open Set

theorem AvramDividend.Classical.recordPartition_Ioc_disjoint
    (u : ℕ → ℝ) (hu : Monotone u)
    (i j : ℕ) (hij : i < j) :
    Disjoint (Set.Ioc (u i) (u (i + 1)))
             (Set.Ioc (u j) (u (j + 1))) := by sorry
