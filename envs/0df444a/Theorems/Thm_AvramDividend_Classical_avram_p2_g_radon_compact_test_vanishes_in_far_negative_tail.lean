-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_compact_test_vanishes_in_far_negative_tail
-- name    : AvramDividend.Classical.avram_p2_g_radon_compact_test_vanishes_in_far_negative_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:20:40.168923+00:00
-- url     : https://prove2.me/theorems/50fcce59-47e5-4e8c-ad6b-1e2f41d4125a
-- title:
--   Compactly supported continuous negative-mark tests vanish on sufficiently far-negative marks
-- statement:
--   Every continuous compactly supported test on the strictly negative real half-line vanishes below some finite negative threshold -R with R positive. This supplies the missing far-negative endpoint support bound so the weighted exponential-coordinate quotient used in the original Lévy small-time rate proof can extend continuously to z=0.
-- source:
--   Mathlib.Topology.Order.Compact: IsCompact.exists_isMinOn; Mathlib.Topology.Algebra.Support: HasCompactSupport and subset_tsupport.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_compact_test_vanishes_in_far_negative_tail
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ x : {x : ℝ // x < 0}, (x : ℝ) < -R → f x = 0 := by sorry
