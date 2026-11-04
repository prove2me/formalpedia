-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_ext_from_comparator_finite
-- name    : AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_ext_from_comparator_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:13:15.892201+00:00
-- url     : https://prove2.me/theorems/fd7b7bda-8f73-41a1-b2dc-8408fdcfa75c
-- title:
--   Dense cutoff tests imply Borel restriction equality with only comparator finiteness
-- statement:
--   Given a Borel comparison measure finite below the real cutoff, equality of all cutoff lower-halfline tests on a dense threshold set forces equality of the two cutoff-restricted Borel measures. The source measure need not have a separately assumed finite cutoff mass: a threshold strictly above the cutoff belongs to the dense test set and proves finiteness.
-- source:
--   Proved cutoff dense extensionality (3f7566ae), plus pinned Dense.exists_seq_strictAnti_tendsto; independent of stochastic rates.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_cutoff_dense_ext_from_comparator_finite
    (μ ν : Measure ℝ) (c : ℝ)
    (hνfin : ν (Iic c) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a ∩ Iic c) = ν (Iic a ∩ Iic c)) :
    μ.restrict (Iic c) = ν.restrict (Iic c) := by sorry
