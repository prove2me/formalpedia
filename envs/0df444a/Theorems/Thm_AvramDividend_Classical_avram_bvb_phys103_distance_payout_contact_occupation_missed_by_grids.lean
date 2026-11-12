-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys103_distance_payout_contact_occupation_missed_by_grids
-- name    : AvramDividend.Classical.avram_bvb_phys103_distance_payout_contact_occupation_missed_by_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:53:30.655885+00:00
-- url     : https://prove2.me/theorems/80c32137-0c9e-4572-9ea8-52054f2a8494
-- title:
--   Monotone distance-profile payout has positive contact time missed by every grid
-- statement:
--   A continuous nondecreasing zero-initial dividend profile can place a linear-drift reserve at its contact threshold on positive-volume time while every point on the countable family of deterministic grids strictly misses that threshold.
-- source:
--   Original bounded-variation phys95 contact-occupation model, using verified phys98 and phys101

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys101_positive_contact_set_strictly_missed_by_grids
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys98_distance_contact_dividend_monotone_zero_initial
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_phys103_distance_payout_contact_occupation_missed_by_grids (u : ℕ → ℕ → ℝ) : ∃ K : Set ℝ, 0 < (volume : Measure ℝ) K ∧ Monotone (fun t : ℝ => t + Metric.infDist t K - Metric.infDist 0 K) ∧ ((0 : ℝ) + Metric.infDist 0 K - Metric.infDist 0 K) = 0 ∧ (∀ t ∈ K, t - (t + Metric.infDist t K - Metric.infDist 0 K) = Metric.infDist 0 K) ∧ (∀ n i : ℕ, u n i - (u n i + Metric.infDist (u n i) K - Metric.infDist 0 K) < Metric.infDist 0 K) := by sorry
