-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_extended_cap_local_C2_restrict
-- name    : AvramDividend.Classical.avram_wave7_07_ubv_extended_cap_local_C2_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:20:10.06006+00:00
-- url     : https://prove2.me/theorems/f4c8b80d-df81-4f56-baa1-9351a32ce1ef
-- title:
--   Extended-real cap UBV C² regularity localises to finite real intervals
-- statement:
--   If w is twice continuously differentiable at every positive reserve with ENNReal.ofReal reserve below the original extended-real admissibility cap C, then w is twice continuously differentiable on (0,R) for each real R with ENNReal.ofReal R<C. The simple monotonicity of ofReal preserves the precise W7-08 domain, including top caps.
-- source:
--   W7-07 source-specific W7-08 finite localisation for compensated negative-jump Taylor generator; no modified canonical target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_ubv_extended_cap_local_C2_restrict
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (R : ℝ) (hRcap : ENNReal.ofReal R < C) :
    ContDiffOn ℝ 2 w (Ioo 0 R) := by sorry
