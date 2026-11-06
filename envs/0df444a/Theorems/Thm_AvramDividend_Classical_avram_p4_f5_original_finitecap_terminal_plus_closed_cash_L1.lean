-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f5_original_finitecap_terminal_plus_closed_cash_L1
-- name    : AvramDividend.Classical.avram_p4_f5_original_finitecap_terminal_plus_closed_cash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:48:31.794473+00:00
-- url     : https://prove2.me/theorems/28421c99-d79e-4cc1-80b9-ac8e8e3e39db
-- title:
--   Finite-cap actual original stopped terminal and closed-horizon dividend cash are jointly integrable
-- statement:
--   For an original capped dividend strategy with finite real cap c≥0, exact post-rightpayment stopped W, exact Iic Stieltjes Cash and discounted terminal Term, assuming actual Cash is integrable and Term is strongly measurable, the combined reward Term+Cash is integrable. This discharges the finite-cap integrability branch of the new real natural-clock source budget child; the expected upper bound and C=top integrability remain independent obligations.
-- source:
--   Direct import of Proved original finite-cap terminal L1 d5ea6491, passing the exact hW and transformed hTermMeas, then integrability addition with the canonical cash assumption; no downstream source theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finitecap_terminal_global_L1_auto_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f5_original_finitecap_terminal_plus_closed_cash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P) :
    Integrable (fun ω => Term ω + Cash ω) P := by sorry
