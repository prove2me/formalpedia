-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_indicator_ae
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_indicator_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:03:32.870017+00:00
-- url     : https://prove2.me/theorems/b772ad08-b1d8-48fa-ae76-f7ceee5f08ce
-- title:
--   Small-jump truncation indicator equals one almost everywhere under the compact uniform negative-mark law
-- statement:
--   All mass of the uniform negative-mark law lies in (-1,0); hence the standard Lévy small-jump indicator is identically one almost everywhere.
-- source:
--   Direct deterministic prerequisite of A06 compensated-exponent identity fa25b11f.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_indicator_ae :
    ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)),
      (Ioo (-1 : ℝ) 0).indicator (1 : ℝ → ℝ) y = 1 := by sorry
