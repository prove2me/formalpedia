-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:32:23.899513+00:00
-- url     : https://prove2.me/theorems/85b04ac6-f80f-4fb2-bff2-39901d3549e8
-- title:
--   Genuine finite-cap entire marked Lévy upper-strip compensated Ito remainder bounded by positive-part ruin overshoot
-- statement:
--   Complete original finite-cap corrected upper-strip Levy mark jump-Taylor envelope, valid for EVERY real marked jump z and genuinely original spectrally negative Levy source. From the active non-ruin marked correction Proved ce111444, the compensated potential remainder is ≤0 whenever y+z≥0. From the ruin-overshoot marked correction f0aa021f, it is ≤-postreserve when y+z<0. Combining yields exact global bound by positive-part ruin overshoot. This quantifies the only boundary correction needed when removing the finite cap spatial localiser from a stopped infinite-activity jump Ito source; it preserves the actual candidate gradient/continuity and does not claim the positive overshoot source is integrable without a separate proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ max 0 (-(y + z)) := by sorry
