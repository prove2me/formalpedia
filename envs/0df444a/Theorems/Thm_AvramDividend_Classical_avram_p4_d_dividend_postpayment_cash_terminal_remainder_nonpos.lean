-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postpayment_cash_terminal_remainder_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_postpayment_cash_terminal_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:44:59.18052+00:00
-- url     : https://prove2.me/theorems/d7a848b8-1ca7-4568-90a2-39e9b627516b
-- title:
--   Actual original postpayment stopped W and complete Cash have nonpositive dividend remainder at zero or before ruin
-- statement:
--   At the original measurable stopped clock, substitute the exact piecewise post-right-payment terminal W and actual discounted dividendMeasure Cash, including time zero, terminal right atom and diffuse/singular-continuous payments. On the zero-or-strictly-pre-ruin branch, the full original payment remainder relative to the cap-linear extension V is nonpositive, without any extra boundary localisation. The positive-time ruin branch remains separate. This is a deterministic source-backed Stieltjes identity; it does not assert the stochastic Ito-Meyer chain rule or integrability.
-- source:
--   Avram, Palmowski and Pistorius Proposition 4(i), equation (5.13); original Proved full Stieltjes sign b7f6754b-bb40-4d86-bd48-aae4411986f7 and zero-or-strict original payment domain bfe4a214-2dc7-40dc-b43d-19316d917a2e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_postpayment_cash_terminal_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    Cash ω + (V (W ω) - V (x + X.X (τ ω) ω)) ≤ 0 := by sorry
