-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_compact_clock_closed_cash_L1
-- name    : AvramDividend.Classical.avram_ubv_top9_original_any_compact_clock_closed_cash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:05:24.908598+00:00
-- url     : https://prove2.me/theorems/a8ddfafe-2688-421d-9f55-a0d088a7a7ba
-- title:
--   Original bounded-upcross any stopped clock has L1 full discounted post-right reward and closed cash
-- statement:
--   For any original admissible dividend process, an earlier measurable right-continuous stopping clock with a deterministic upper bound on the stopped original Lévy value inherits L1 terminal-plus-closed-Iic cash from L1 of the full horizon cash, without a global bound on the HJB potential or a finite surplus cap.
-- source:
--   Source-exact arbitrary-clock adaptation of Proved F12 1a91b59a localization: F15 compact halfline bound, F18 physical postpayment upper reserve, original stopped W measurability, localise_discounted_terminal_integrable_of_ae_bound, and ordered-clock closed-Iic Stieltjes cash L1 6a275c18. Intended downstream of top9 upcross localisation and before Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_any_compact_clock_closed_cash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρmeas : Measurable (fun ω => (ρ ω : ℝ)))
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (K : ℝ) (hXBound : ∀ ω, X.X (ρ ω) ω ≤ K)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Integrable F P := by sorry
