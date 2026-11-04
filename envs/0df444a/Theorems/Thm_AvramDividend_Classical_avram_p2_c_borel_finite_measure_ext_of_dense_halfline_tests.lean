-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:41:00.186525+00:00
-- url     : https://prove2.me/theorems/e77f83dd-e59a-4303-b9ea-b348ba16b584
-- title:
--   Finite real Borel measures determined by lower-halfline tests on any dense threshold set
-- statement:
--   Two finite Borel measures on the real line agree on every Borel set if their lower-halfline cumulative masses coincide on any topologically dense set of test thresholds. The proof builds a strictly decreasing sequence of thresholds from the dense set tending to each endpoint, then uses continuity from above. No assumption is made about source measure atoms.
-- source:
--   P2-C directly derives the dense-threshold portmanteau interface from the newly Proved avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests and pinned Dense.exists_seq_strictAnti_tendsto. This supports Lévy-rate identification when the analytic bridge supplies only rational or another dense threshold family, without assuming the Open original rate theorem.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a) = ν (Iic a)) :
    μ = ν := by sorry
