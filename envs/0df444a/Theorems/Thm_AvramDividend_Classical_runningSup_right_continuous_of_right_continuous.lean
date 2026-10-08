-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
-- name    : AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T08:12:53.75098+00:00
-- url     : https://prove2.me/theorems/f0c2320c-8218-484b-9054-75090ac9c401
-- title:
--   Monotone running supremum is right-continuous when the underlying path is right-continuous
-- statement:
--   Let M(t) be a nondecreasing running supremum of a real-valued path f, with every path value f(u) bounded above by M(u), and with M(t) represented as the supremum of f over [0,t]. If f is right-continuous, then M is right-continuous at every nonnegative time. For any bound b>M(t), choose an intermediate m. Right-continuity keeps f below m immediately to the right of t; past values are already below M(t)<m, so the whole running supremum stays below m<b.
-- source:
--   Reusable order-topology helper for the Avram Dividend barrier admissibility witness. No local Lean verification; intended for remote Prove2Me checking.

import Mathlib

open Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
    (f M : ℝ≥0 → ℝ)
    (hM : Monotone M)
    (hdom : ∀ u, f u ≤ M u)
    (hrepr : ∀ t, M t =
      ⨆ u : Set.Icc (0 : ℝ≥0) t, f u.1)
    (hfRight : ∀ t, Tendsto f (𝓝[≥] t) (𝓝 (f t)))
    (t : ℝ≥0) :
    ContinuousWithinAt M (Set.Ici t) t := by
  sorry
