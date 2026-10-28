-- Prove2me | Theorems.Thm_AvramDividend_Classical_downward_left_jump_add_continuous_iff
-- name    : AvramDividend.Classical.downward_left_jump_add_continuous_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:58:30.633885+00:00
-- url     : https://prove2.me/theorems/54de2750-535c-427f-9967-cec91af8b910
-- title:
--   A real càdlàg path has a genuine downward left jump exactly when its sum with a continuous drift does
-- statement:
--   For arbitrary real-valued functions f and g on nonnegative time, if g is continuous at t then f has a strict downward jump at t with finite left limit if and only if the pointwise sum f+g has a strict downward jump at t with finite left limit. The left limit shifts by g(t), and strict jump inequality is preserved. This deterministic result is required to identify intrinsic downward jump events of a canonical Lévy–Itô process after adding deterministic linear drift, smooth compensators or a continuous Gaussian component, without asserting the Poisson mark-to-path jump identification itself.
-- source:
--   Basic filter Tendsto.add/sub and continuousAt.tendsto. The canonical LeanLevy/RandomMeasure/LevyJumpPath.lean decomposition is drift + large-jump sum + compensated small-jump path. Used to remove continuous drift from intrinsic path-jump counts.

import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.NNReal.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.downward_left_jump_add_continuous_iff
    (f g : ℝ≥0 → ℝ) (t : ℝ≥0) (hg : ContinuousAt g t) :
    (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l) ∧ f t < l) ↔
    (∃ l : ℝ, Tendsto (fun s => f s + g s)
      (nhdsWithin t (Iio t)) (nhds l) ∧ f t + g t < l) := by sorry
