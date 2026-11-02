-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_positive_part_domination
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_positive_part_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:41:38.490631+00:00
-- url     : https://prove2.me/theorems/f7e3602f-6f61-438e-a565-cd6db41ec536
-- title:
--   Original UBV exact Chat 06 piecewise stopped Ito reward positive-part bounded by w
-- statement:
--   For the actual source process X and admissible D with the corrected core's unbounded-variation and w(0)>=0/interior gradient conditions, take Chat 06's exact piecewise stopped terminal reward W: before ruin use x+X_tau-rightLimit D_tau, otherwise use riskProcess at tau. Then max(0,W(ω))≤w(W(ω)) holds for every original path, including creeping to reserve zero, ruin at zero, negative overshoot and any cap including C=0 or infinity. This combines the two already Proved all-cap prepayment and postpayment positive-part theorems. It strengthens the sign premise used by Chat 06 without any martingale or Stieltjes integration.
-- source:
--   Open Chat 06 expected budget target b02af371-7a57-4d30-9a67-a2a03ebab34b exact W; source all-cap prepayment terminal positive-part 2b04d61b-0c38-44e4-ba16-ea6843d0c45e and postpayment 9ae5dedd-b82e-4205-9f96-af361b8e4e08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_positive_part_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, max 0 (W ω) ≤ w (W ω) := by sorry
