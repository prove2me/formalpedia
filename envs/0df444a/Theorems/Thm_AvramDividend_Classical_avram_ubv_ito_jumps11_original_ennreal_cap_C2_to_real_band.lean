-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:35:46.135349+00:00
-- url     : https://prove2.me/theorems/bf798010-5676-4ded-a6c5-751564c43f54
-- title:
--   Original HJB ENNReal cap C2 smoothness transfers to every real interior source band
-- statement:
--   The genuine original dividend candidate smoothness hypothesis on the strict ENNReal-capped domain implies two continuous derivatives on every positive real interval (0,c) lying weakly below the cap. This is the missing source-regularity coercion for finite-band original Lévy Ito-Meyer and stopped Taylor compensation. It does not assert the global Ito formula, Gaussian martingale, or dividend residual inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
    (C : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcC : ENNReal.ofReal c ≤ C)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContDiffOn ℝ 2 w (Ioo (0 : ℝ) c) := by sorry
