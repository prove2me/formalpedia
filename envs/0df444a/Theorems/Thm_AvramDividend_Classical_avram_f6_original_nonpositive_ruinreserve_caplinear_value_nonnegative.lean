-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_nonpositive_ruinreserve_caplinear_value_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_nonpositive_ruinreserve_caplinear_value_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:33:51.322577+00:00
-- url     : https://prove2.me/theorems/94fc737b-9a74-4c65-927f-2e0acae01a70
-- title:
--   Original ruin overshoot caplinear terminal is nonnegative on nonpositive reserve
-- statement:
--   At the actual ruin contact or negative-jump overshoot when the original reserve z is nonpositive, the canonical caplinear w remains w(z), since ENNReal.ofReal(z)=0<=C. The original ruin reward is nonnegative: w(z)=0 for z<0 and w(0)>=0. This uses the original surplus convention and is independent of assumptions on w above finite C.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_nonpositive_ruinreserve_caplinear_value_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (z : ℝ) (hz : z ≤ 0) :
    0 ≤ (if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) := by sorry
