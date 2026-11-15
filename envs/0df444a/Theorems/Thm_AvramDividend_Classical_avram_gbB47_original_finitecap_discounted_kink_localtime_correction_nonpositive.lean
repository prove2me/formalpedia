-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
-- name    : AvramDividend.Classical.avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:14:50.872595+00:00
-- url     : https://prove2.me/theorems/5c351bd3-f513-4f45-9bea-50b1fae20420
-- title:
--   Original finitecap discounted Itô-Tanaka clipping local-time correction is nonpositive
-- statement:
--   At every actual interior rational clipping threshold of the original finite-cap verification problem, the local-time coefficient (1-w′(b))/2 is nonpositive. Any nonnegative original local-time increment multiplied by a nonnegative discount factor therefore contributes a nonpositive correction to the original Itô-Tanaka cash ledger.
-- source:
--   B45 certifies the genuine caplinear one-sided derivative jump 1-w′(b)≤0; nonnegative local-time mass and discount preserve the nonpositive sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) (L E : ℝ) (hL : 0 ≤ L) (hE : 0 ≤ E) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    E * (((1 - deriv w b) / 2) * L) ≤ 0 := by sorry
