-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
-- name    : AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_cash_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:52:51.302437+00:00
-- url     : https://prove2.me/theorems/9092f3d2-6797-4a1a-a580-2fb06ae26860
-- title:
--   Original stopped physical payoff and inclusive cash in the exact real caplinear continuation
-- statement:
--   For any genuine original bounded subordinate stopping clock, the actual discounted w terminal plus paymentTimes intersect Iic discounted cash is exactly the real C=top or slope-one finitecap continuation V evaluated on the original zero/pre-ruin/rightLimit and ruin/riskProcess branches. The theorem bridges the already proved true stopped terminal and the original physically capped Stieltjes/Ito grid V, with no above-cap differentiability hypothesis and no abstract martingale witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_cash_exact
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
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω,
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      F k ω = Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
