-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_masked_preruin_pointwise_signed_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_p4f_masked_preruin_pointwise_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:35:45.090761+00:00
-- url     : https://prove2.me/theorems/8c2fadad-b069-4213-b5b8-c97d05623f97
-- title:
--   Original P4-F pre-ruin masked dividend cash correction is pathwise nonpositive and integrable
-- statement:
--   The original closed-horizon right-continuous dividend pathwise budget supplies Cash plus postpayment V minus pre-control Lévy V nonpositive at every eligible stopped pre-ruin path, including time zero and the surviving horizon. The event-masked signed remainder is integrable given actual Cash, source V and stopped controlled V integrability, and has pointwise sign, with the positive-ruin event isolated.
-- source:
--   Proved P4-D original pathwise postpayment cash terminal remainder UUID d7a848b8-1ca7-4568-90a2-39e9b627516b and Mathlib Integrable.indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postpayment_cash_terminal_remainder_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_p4f_masked_preruin_pointwise_signed_L1
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
    (s : Set Ω)
    (hs : s = {ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hsMeas : MeasurableSet s)
    (hCashI : Integrable Cash P)
    (hAfterI : Integrable (fun ω => V (W ω)) P)
    (hBeforeI : Integrable
      (fun ω => V (x + X.X (τ ω) ω)) P) :
    let H : Ω → ℝ := s.indicator (fun ω =>
      Cash ω + V (W ω) - V (x + X.X (τ ω) ω))
    Integrable H P ∧ ∀ ω, H ω ≤ 0 := by sorry
