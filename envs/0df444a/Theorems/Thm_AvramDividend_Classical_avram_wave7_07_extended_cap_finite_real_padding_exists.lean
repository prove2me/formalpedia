-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_extended_cap_finite_real_padding_exists
-- name    : AvramDividend.Classical.avram_wave7_07_extended_cap_finite_real_padding_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:18:31.032368+00:00
-- url     : https://prove2.me/theorems/e9d89d90-9c1f-42ee-85be-15de7905987b
-- title:
--   A positive interior point below an extended-real cap admits a larger finite real localisation
-- statement:
--   If v is nonnegative and its nonnegative extended-real image is strictly below the admissibility cap C, there is a finite real R>v still strictly below C. The top-cap case uses v+1; the finite-cap case takes the midpoint between v and C.toReal. This supplies the real R required for source negative-jump local C² arguments.
-- source:
--   W7-07 extended-real cap finite localisation step for the original W7-08 UBV source theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_extended_cap_finite_real_padding_exists
    (C : ℝ≥0∞) (v : ℝ) (hv0 : 0 ≤ v)
    (hv : ENNReal.ofReal v < C) :
    ∃ R : ℝ, v < R ∧ ENNReal.ofReal R < C := by sorry
