-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightContinuous_negative_right_interval
-- name    : AvramDividend.Classical.rightContinuous_negative_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:14:48.506359+00:00
-- url     : https://prove2.me/theorems/9e783a57-60b7-4652-ba81-8f2267ac89d5
-- title:
--   A negative value of a right-continuous nonnegative-time path persists on a nontrivial right interval
-- statement:
--   For any real-valued path on nonnegative times, if the path is continuous from the right at time t and f(t)<0, then some interval [t,u) with u>t consists of strictly negative values. This precise topological fact is required to identify a downward-regularity event with its countable dense observation-grid event under the spectrally negative Lévy process's right-continuity field. It is independent of stochastic independence or any regularity assertion.
-- source:
--   Elementary topology of right-continuous (càdlàg) paths, as used to reduce Lévy half-line regularity to countably many observation times.

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.Basic

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.rightContinuous_negative_right_interval
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hcont : ContinuousWithinAt f (Ici t) t)
    (hneg : f t < 0) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → f s < 0 := by sorry
