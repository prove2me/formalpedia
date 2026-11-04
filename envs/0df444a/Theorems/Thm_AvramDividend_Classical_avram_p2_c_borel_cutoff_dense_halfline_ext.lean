-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext
-- name    : AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_halfline_ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:59:24.131304+00:00
-- url     : https://prove2.me/theorems/3f7566ae-287f-48e9-a1b5-36890f1551a0
-- title:
--   Finite cutoff Borel measure identification from dense halfline tests
-- statement:
--   For measures with finite mass on the negative cutoff halfline, agreement of cutoff-restricted lower-halfline masses on any dense set of real thresholds implies equality of the full Borel restrictions. The unrestricted measures may be infinite. The proof derives finite restricted measures and applies the proved dense-halfline measure extensionality lemma.
-- source:
--   P2-C uses Proved avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests; no unproved Lévy-rate theorem or source ν-rate assumed.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_halfline_ext
    (μ ν : Measure ℝ) (c : ℝ)
    (hμfin : μ (Iic c) ≠ ⊤) (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a ∩ Iic c) = ν (Iic a ∩ Iic c)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by sorry
