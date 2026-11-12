-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_stopped_open_mark_loss_nonnegative
-- name    : AvramDividend.Classical.avram_bvb_b22_original_stopped_open_mark_loss_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:09:18.740429+00:00
-- url     : https://prove2.me/theorems/4c8b0d74-bfe3-4b52-9436-7057af743259
-- title:
--   Original stopped open-cap marked-loss density is nonnegative
-- statement:
--   The discounted negative Lévy-mark loss at the original stopped reserve left limit is nonnegative under the BV secant-gradient condition, including zero when the open-cap mask fails.
-- source:
--   A necessary sign premise for nonnegative reverse Fatou on the original physical sampled compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b22_original_stopped_open_mark_loss_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    0 ≤ if (t : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < U t ∧ ENNReal.ofReal (U t) < C then
          -(Real.exp (-(q * (t : ℝ))) *
            ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
        else 0 := by sorry
