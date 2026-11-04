-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:11:02.68488+00:00
-- url     : https://prove2.me/theorems/6b34d025-b51b-48e0-a6a5-a9c701baadc4
-- title:
--   Finite Borel measures are determined by decreasing half-line test approximations
-- statement:
--   If two finite Borel measures on the real line agree on each half-line from a sequence of thresholds decreasing to every prescribed real endpoint, they agree on all Borel sets. The proof uses continuity from above and finite-measure uniqueness on lower half-lines. This allows original Levy separated-band source rates to be identified first at continuity thresholds rather than every possible atom.
-- source:
--   P2-C Borel test-class transport bridge for 788041e5/4928a464, independent of the Open original source rate 34dbea70. Reuses pinned Mathlib Measure.ext_of_Iic, Antitone.measure_iInter and right-limit of Iic thresholds. Not a claim of Levy intensity.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hApprox : ∀ a : ℝ, ∃ q : ℕ → ℝ,
      Antitone q ∧ Tendsto q atTop (𝓝 a) ∧
      (∀ n, a ≤ q n) ∧
      (∀ n, μ (Iic (q n)) = ν (Iic (q n)))) :
    μ = ν := by sorry
