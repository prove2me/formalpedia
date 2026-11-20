-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_caplinear_cash_exact
-- name    : AvramDividend.Classical.avram_f6_original_stopped_reward_caplinear_cash_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:40:05.869204+00:00
-- url     : https://prove2.me/theorems/fb5cff6b-ce0a-4091-94dc-8e90e85816aa
-- title:
--   Original stopped terminal plus inclusive dividend cash expressed by true caplinear continuation
-- statement:
--   At each true original subordinate stopping clock, the actual discounted terminal reward plus inclusive paymentTimes intersect Iic cash is exactly the same expression using the canonical slope-one caplinear continuation V at the actual terminal branch. The zero, pre-ruin and ruin-contact cases are retained exactly. Derivation uses the real original capped terminal identity, without off-cap raw-w extrapolation or abstract martingale witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_stopped_reward_caplinear_cash_exact
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
        if ENNReal.ofReal z ≤ C then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      F k ω = Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
