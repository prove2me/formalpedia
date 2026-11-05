-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:03:04.296075+00:00
-- url     : https://prove2.me/theorems/9756f094-e818-4164-909c-c9bcc340204c
-- title:
--   Joint original stopped dividend-gradient measurability from the actual source left and right limits
-- statement:
--   For the original spectrally negative Lévy process and adapted right-dividend control, joint measurability of the source left limit and dividend right limit, measurability of the literal derivative of the value function, and measurability of the exact pre-ruin closed-horizon window give joint strong measurability of the source-chronological discounted signed dividend-gradient integrand. This supplies the concrete joint-measurability input of the P4-D measurable-kernel Bochner integral bridge.
-- source:
--   Original source SpectrallyNegativeLevy, IsDividendStrategy, leftLim, rightLimit and paymentTimes, composed with pinned Mathlib Measurable.indicator and Real.exp measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (hXL : Measurable (fun p : Ω × ℝ =>
      Function.leftLim (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal))
    (hDR : Measurable (fun p : Ω × ℝ =>
      rightLimit D p.2.toNNReal p.1))
    (hDeriv : Measurable (deriv w))
    (hWindow : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2) := by sorry
