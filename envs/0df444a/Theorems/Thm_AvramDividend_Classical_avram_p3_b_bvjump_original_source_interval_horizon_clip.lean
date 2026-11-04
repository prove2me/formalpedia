-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_interval_horizon_clip
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_source_interval_horizon_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:32:55.317401+00:00
-- url     : https://prove2.me/theorems/4ed4d779-4c91-4051-86b2-42e7cc761c7c
-- title:
--   Original nonnegative source jump interval clips exactly at a finite physical horizon
-- statement:
--   At the original NNReal physical clock, the stopped finite source rectangle (s,t]∩[0,T] is exactly (s,min(t,T)]. This is the deterministic horizon clipping identity needed to transport P2 original jump-count rate to the original stopped predictable product, including disjoint/zero-length intervals without a positivity assumption. No new stochastic assumptions or probability spaces.
-- source:
--   Mathlib Set interval membership and `le_min_iff`; Avram Proposition 4(i) finite horizon.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_source_interval_horizon_clip
    (s t T : ℝ≥0) :
    (Ioc s t ∩ Iic T) = Ioc s (min t T) := by sorry
