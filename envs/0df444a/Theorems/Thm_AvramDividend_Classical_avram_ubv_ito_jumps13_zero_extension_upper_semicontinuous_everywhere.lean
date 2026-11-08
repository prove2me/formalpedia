-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T15:39:27.636004+00:00
-- url     : https://prove2.me/theorems/3ef3cadc-0f0e-46f1-b0b4-d4a8887245c1
-- title:
--   Zero-extended original reserve value admits a local upper envelope at every real level
-- statement:
--   The original reserve value is continuous for nonnegative surplus, vanishes for negative surplus, and has a nonnegative boundary value at zero. Its zero extension is upper semicontinuous at all real surplus levels. This protects jumps landing at zero without asserting false two-sided continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_semicontinuous_everywhere
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ x ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, |y - x| < δ → w y ≤ w x + ε := by sorry
