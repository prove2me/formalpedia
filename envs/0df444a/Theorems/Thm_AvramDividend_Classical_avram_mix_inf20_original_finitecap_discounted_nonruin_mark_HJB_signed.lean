-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:27:40.67002+00:00
-- url     : https://prove2.me/theorems/035eb378-857f-4cf7-b7d2-ab862c806848
-- title:
--   Original finitecap discounted stopped above-cap Lévy nonruin jump HJB Taylor term is nonpositive
-- statement:
--   Exact original stopped discounted finite-cap spectrally negative Lévy marked negative-jump HJB signed remainder on the non-ruin postmark event. For premark reserve y>C and postmark y+z≥0, use Proved ce111444 caplinear gradient-secancy to show compensated mark remainder ≤0. Multiplying by the actual strictly positive e^{-qt} discount preserves nonpositivity at every physical time, with no stochastic expectation. The theorem is a ready-to-integrate building block for finite-cap physical stopped Gaussian-jump Ito certificate 76d39cdc. Ruin overshoot is handled separately by f0aa021f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q t y z : ℝ) (hy : C.toReal < y) (hz : 0 ≤ y + z) :
    let V : ℝ → ℝ := fun s =>
      if s ≤ C.toReal then w s else w C.toReal + (s - C.toReal)
    Real.exp (-(q * t)) *
      (V (y + z) - V y - deriv V y * z) ≤ 0 := by sorry
