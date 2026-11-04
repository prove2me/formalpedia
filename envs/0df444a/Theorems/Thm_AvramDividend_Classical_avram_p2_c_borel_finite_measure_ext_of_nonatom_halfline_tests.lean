-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:07.245122+00:00
-- url     : https://prove2.me/theorems/079258b1-279f-4eba-9e2b-0f323301814d
-- title:
--   Finite Borel measures agree when half-line masses agree at every nonatom threshold
-- statement:
--   Two finite Borel measures on the real line agree on every Borel set if their lower-half-line cumulative masses coincide at every point where the second measure has no atom. Atoms are countable, their complement is dense, and decreasing nonatom thresholds approach every endpoint. This is a portmanteau-ready Borel uniqueness bridge for original Levy separated-band jump rates.
-- source:
--   P2-C conditional Borel extension of 788041e5, using proposed avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests, pinned Measure.countable_meas_level_set_pos, Set.Countable.dense_compl and Dense.exists_seq_strictAnti_tendsto. Does not import or assume the Open original Levy rate theorem 34dbea70.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hTests : ∀ a : ℝ, ν {a} = 0 → μ (Iic a) = ν (Iic a)) :
    μ = ν := by sorry
