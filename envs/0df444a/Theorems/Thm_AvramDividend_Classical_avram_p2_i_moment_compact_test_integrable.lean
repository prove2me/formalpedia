-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_integrable
-- name    : AvramDividend.Classical.avram_p2_i_moment_compact_test_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:26:41.392984+00:00
-- url     : https://prove2.me/theorems/f2765a52-d357-4917-84ef-4e573ab7a54d
-- title:
--   Continuous test vanishing outside the unit interval is integrable for any finite measure
-- statement:
--   A continuous real-valued test g that vanishes for z≤0 and z≥1 has compact support contained in [0,1] and is integrable against any finite positive Borel measure on the real line. This bridges the test-class assumptions in the main moment-to-continuous-test theorem with the integrability premises of the quantitative integral error estimate, without assuming the approximating measures are supported on [0,1].

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_compact_test_integrable
    (μ : Measure ℝ) (hfinite : μ Set.univ < ⊤)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Integrable g μ := by sorry
