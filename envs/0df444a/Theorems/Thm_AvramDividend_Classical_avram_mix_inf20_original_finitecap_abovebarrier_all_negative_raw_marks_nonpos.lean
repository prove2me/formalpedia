-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:30:52.255118+00:00
-- url     : https://prove2.me/theorems/22675bab-0fcd-4fa4-b04f-c7f7aacc318a
-- title:
--   Genuine finitecap original Lévy large negative jump raw caplinear reserve potential decreases including ruin overshoot
-- statement:
--   Original finite-cap large-negative-jump Lévy marked raw potential decrease at a premark reserve strictly above cap. Under candidate w0≥0, continuity, interior derivative≥1, zero below ruin, every strictly negative marked increment z lowers the caplinear continuation V: V(y+z)-V(y)≤0, including negative ruin overshoots. Prove from server-Proved ce111444 active nonruin compensated sign and f0aa021f ruin overshoot compensated correction, with V'(y)=1 already built into both child results. This establishes the correct uncompensated large-jump sign for the actual Lévy generator and does not require ∫|z| on heavy negative tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y ≤ 0 := by sorry
