-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_NNReal_countable_dense_clock_with_zero
-- name    : AvramDividend.Classical.avram_gbB32_NNReal_countable_dense_clock_with_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T19:08:08.139345+00:00
-- url     : https://prove2.me/theorems/90557562-f2b8-482e-89bd-66835b4c3174
-- title:
--   Choose a countable dense nonnegative physical grid clock containing time zero
-- statement:
--   Exhibit a genuinely countable dense set of NNReal physical times containing 0, by adjoining zero to a countable dense subset of the separable nonnegative real line. This discharges the final free source clock-set assumptions for Gaussian stopped first hitting source geometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_NNReal_countable_dense_clock_with_zero :
    ∃ (S : Set ℝ≥0), S.Countable ∧ Dense S ∧ (0 : ℝ≥0) ∈ S := by sorry
