-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:36:06.301203+00:00
-- url     : https://prove2.me/theorems/ab9ed3a1-ff2b-4989-98af-f65f3a0536b6
-- title:
--   Compact strictly negative tests vanish uniformly near the zero jump mark
-- statement:
--   For every continuous real test with compact topological support contained in the strictly negative half-line, prove an explicit positive neighbourhood of zero on which the test vanishes. Derive the gap from the already proved compact support separation theorem and eliminate values outside topological support. This source-independent analytic bridge discharges the vanishing condition for P2-A original Lévy pathwise grid-jump limits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_compact_negative_support_separation
open MeasureTheory Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, |z| < ρ → g z = 0 := by sorry
