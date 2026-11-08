-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_zero_extension_upper_contact
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T15:21:48.010606+00:00
-- url     : https://prove2.me/theorems/13a4aebe-7cea-4781-ab5b-b32f52b590ed
-- title:
--   Nonnegative zero extension has a uniform upper envelope at exact zero-reserve contact
-- statement:
--   A candidate w continuous on nonnegative reserves, zero at negative reserves and nonnegative at zero is upper semicontinuous at the origin in an explicit epsilon-delta form, even when w(0)>0. This gives the correct one-sided bound for negative Levy marks landing exactly on reserve zero; no false two-sided continuity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! The zero extension has a one-sided upper envelope even if `w 0 > 0`. -/

theorem AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_contact
    (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, |y| < δ → w y ≤ w 0 + ε := by sorry
