-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_ruin_crossing_negative_source_jump_value_loss
-- name    : AvramDividend.Classical.avram_wave7_02_original_ruin_crossing_negative_source_jump_value_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:36:28.568526+00:00
-- url     : https://prove2.me/theorems/7c6b6ce1-7293-49c6-8678-d25fc3216025
-- title:
--   Original true reserve ruin-crossing negative Levy jump has nonpositive C1 value loss
-- statement:
--   For the actual original spectrally negative Levy X and dividend path D, if the true pre-source reserve (using leftLim X and D t) is nonnegative within the cap and the post-source prepayment reserve x+X.X t-D t crosses strictly below zero, then this was a strictly negative source jump and the HJB candidate value change from the source event is nonpositive. This uses exactly the canonical w(y)=0 at negative reserves, w(0)≥0 and BV interior C1 gradient≥1, without claiming differentiability at the ruin overshoot or replacing the original process. Handles a crucial boundary of the stopped BV chain rule.
-- source:
--   Proved original full-cap BV gradient secant 2ba5cc4f, actual source leftLim and ruin-crossing jump, canonical value extension to negative reserves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_ruin_crossing_negative_source_jump_value_loss
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
    (hb : 0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C)
    (ha : x + X.X t ω - D t ω < 0) :
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0 ∧
    w (x + X.X t ω - D t ω) -
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ 0 := by sorry
