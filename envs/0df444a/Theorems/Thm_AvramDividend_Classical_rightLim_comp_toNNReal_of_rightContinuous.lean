-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
-- name    : AvramDividend.Classical.rightLim_comp_toNNReal_of_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:13:56.551278+00:00
-- url     : https://prove2.me/theorems/95b3270f-126e-4201-8e6b-b883590393b3
-- title:
--   Real-time right limit of a right-continuous nonnegative-time path
-- statement:
--   For any right-continuous real-valued function f on nonnegative real time, extending it to real time by r↦f(r.toNNReal) preserves the value of its right limit at every real r. This handles negative arguments by clipping time to zero and provides the limit identity needed for Stieltjes dividend measures.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.NNReal.Lemmas

open Set Topology
open scoped NNReal

theorem AvramDividend.Classical.rightLim_comp_toNNReal_of_rightContinuous
    (f : ℝ≥0 → ℝ)
    (hf : ∀ s : ℝ≥0, ContinuousWithinAt f (Set.Ici s) s)
    (r : ℝ) :
    Function.rightLim (fun s : ℝ => f s.toNNReal) r = f r.toNNReal := by sorry
