-- Prove2me | Theorems.Thm_AvramDividend_Classical_left_jump_magnitude_gt_add_continuous_iff
-- name    : AvramDividend.Classical.left_jump_magnitude_gt_add_continuous_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:58:37.122835+00:00
-- url     : https://prove2.me/theorems/3e55bb2e-7f03-4e4c-b01a-de40284487cf
-- title:
--   Left-jump magnitudes are unchanged by adding any real-valued continuous path
-- statement:
--   For a real càdlàg-type path f and any perturbation g continuous at time t, the strict left-jump size condition f(t−)-f(t)>r is equivalent to the same strict threshold for f+g, for every real threshold r. The left limit shifts by g(t), and the exact jump difference is invariant. This allows the pathwise negative-jump band detector to disregard the deterministic drift and Brownian continuous components of a Lévy–Itô construction, with no distributional assumptions.
-- source:
--   Pinned Mathlib continuousAt.tendsto, Tendsto.add/sub, polynomial ring equality. Supports intrinsic path-jump-count identification for the source-faithful LeanLevy/RandomMeasure/LevyJumpPath.lean process.

import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.left_jump_magnitude_gt_add_continuous_iff
    (f g : ℝ≥0 → ℝ) (t : ℝ≥0) (hg : ContinuousAt g t) (r : ℝ) :
    (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l) ∧
      r < l - f t) ↔
    (∃ l : ℝ, Tendsto (fun s => f s + g s)
      (nhdsWithin t (Iio t)) (nhds l) ∧
      r < l - (f t + g t)) := by sorry
