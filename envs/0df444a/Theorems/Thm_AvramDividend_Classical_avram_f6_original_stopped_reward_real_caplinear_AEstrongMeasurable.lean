-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_AEstrongMeasurable
-- name    : AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_AEstrongMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:20:20.133552+00:00
-- url     : https://prove2.me/theorems/b16ec1c4-a01b-4c2f-9337-0f460737227a
-- title:
--   Original caplinear stopped terminal and inclusive dividend cash a.e. measurable from true reward
-- statement:
--   The actual original subordinate stopped reward, expressed with the true caplinear extension of w, ruin-contact branch and inclusive paymentTimes Iic dividendMeasure cash, is AE strongly measurable whenever the original F(k) is integrable. Use the published source-exact stopped payoff identity; no invented process, extension or martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_AEstrongMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) 
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, AEStronglyMeasurable (fun ω =>
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
