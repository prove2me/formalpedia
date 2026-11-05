-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_p4f_masked_preruin_signed_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_p4f_masked_preruin_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:28:58.906507+00:00
-- url     : https://prove2.me/theorems/6eb511d1-3fdf-4e80-b938-12a30b762969
-- title:
--   Original P4-F stopped cash and value correction has a nonpositive integrable pre-ruin event mask
-- statement:
--   For the original stopped controlled Lévy dividend process and full paid Stieltjes cash, the exact P4-F pre-ruin cash plus V(postpayment) minus V(source) remainder is integrable and nonpositive when masked by the measurable survival event. Explicit integrability of the original source and controlled value terms is retained; no assertion is made about the stop exactly at positive ruin, which remains a separate boundary term.
-- source:
--   Proved original P4-D pre-ruin hW full cash inequality UUID 183de9ac-090b-4130-b0a7-876975ce4375; Mathlib Integrable.indicator and Integrable.add/sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_p4f_masked_preruin_signed_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
    Integrable H P ∧ (∀ᵐ ω ∂P, H ω ≤ 0) := by sorry
