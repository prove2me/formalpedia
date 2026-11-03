-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
-- name    : AvramDividend.Classical.avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:46:27.29916+00:00
-- url     : https://prove2.me/theorems/2e7a3f7a-e766-4fe8-9d2c-3a2723e4cff0
-- title:
--   Choose a finite C² real cutoff beyond a positive reserve strictly below original UBV cap
-- statement:
--   Given W7-08's original extended-real cap and positive C² regularity domain, and a finite nonnegative reserve v strictly under the cap, construct an actual finite real R>v still under the cap and inherit ContDiffOn ℝ 2 w on (0,R). Combine exact original W7-07 padding and smoothness restriction lemmas.
-- source:
--   W7-07 direct real-localisation handoff to W7-08 source negative-jump Taylor generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_extended_cap_finite_real_padding_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_extended_cap_local_C2_restrict

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
    (w : ℝ → ℝ) (C : ℝ≥0∞) (v : ℝ)
    (hv0 : 0 ≤ v) (hvC : ENNReal.ofReal v < C)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ R : ℝ, v < R ∧ ENNReal.ofReal R < C ∧
      ContDiffOn ℝ 2 w (Ioo 0 R) := by sorry
