-- Prove2me | Theorems.Thm_AvramDividend_Classical_counting_delta_unif_integrable
-- name    : AvramDividend.Classical.counting_delta_unif_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:35:31.282198+00:00
-- url     : https://prove2.me/theorems/da41882b-819f-4e20-9d40-11b4df6ab3d9
-- title:
--   Moving singleton indicator family is uniformly absolutely integrable on count measure
-- statement:
--   The family n ↦ 1_{n} on the infinite counting measure is uniformly integrable in the measure-theoretic small-set absolute continuity sense: each restriction to a measurable set has L1 norm at most the counting measure of that set. This is a separate reusable certificate for the infinite-measure Vitali counterexample.
-- source:
--   Original mathematical counterexample to arbitrary-mass Vitali convergence

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.counting_delta_unif_integrable :
    UnifIntegrable (fun n : ℕ => ({n} : Set ℕ).indicator
      (fun _ => (1 : ℝ))) 1 (Measure.count : Measure ℕ) := by sorry
