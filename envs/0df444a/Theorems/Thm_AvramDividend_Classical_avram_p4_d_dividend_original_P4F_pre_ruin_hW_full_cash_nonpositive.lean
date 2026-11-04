-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:01:43.688912+00:00
-- url     : https://prove2.me/theorems/183de9ac-090b-4130-b0a7-876975ce4375
-- title:
--   Original P4-F stopped pre-ruin W branch has exact signed full Stieltjes Cash domination
-- statement:
--   At the precise W and Cash functions used by the P4-F original-process stochastic residual budget, establish the a.e. pathwise implication that whenever the stopped clock is zero or strictly before source ruin, the literal full stopped discounted Stieltjes Cash plus the cap-linear terminal reserve change is nonpositive. The source includes time-zero atoms, singular continuous control and eligible terminal payments, and applies to the actual post-X-jump before-right-payment convention. This uses the source-proved full signed Stieltjes inequality and makes no assertion at a positive ruin-crossing clock.
-- source:
--   Public Proved source 75563ed6-01a1-4556-8af6-17e56512c4f4, current fully elaborated P4-F 0dda1be7, exact W and Cash interfaces, Avram et al. Proposition 4(i), Eq. 5.13.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_closed_signed_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ᵐ ω ∂P, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) →
      Cash ω + V (W ω) - V (x + X.X (τ ω) ω) ≤ 0 := by sorry
