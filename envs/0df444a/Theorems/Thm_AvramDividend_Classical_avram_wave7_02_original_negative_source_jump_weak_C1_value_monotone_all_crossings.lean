-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
-- name    : AvramDividend.Classical.avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:39:22.872746+00:00
-- url     : https://prove2.me/theorems/e76d604b-6de2-4c44-98e3-0f10b3bef3f6
-- title:
--   Actual negative source jump never raises the C1 HJB value, including cap, zero landing and ruin overshoot
-- statement:
--   For actual original spectrally negative Levy X at any time t, with the true pre-source capital x+leftLim X t-D t within nonnegative cap and a downward source jump X.X t≤leftLim X t, the C1 HJB value after the source jump is at most its pre-source value. Handles strictly positive landing, landing exactly at 0, and negative ruin overshoot without requiring differentiability outside the positive interior; uses w0≥0 and the zero extension below zero. The source event is separated from a simultaneous right-dividend jump, which occurs after source adjustment.
-- source:
--   Proved original full-cap weak C1 gradient secant 2ba5cc4f, original pre/post source reserve chronology and negative-value extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hMark : X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    (hb : 0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    w (x + X.X t ω - D t ω) ≤
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) := by sorry
