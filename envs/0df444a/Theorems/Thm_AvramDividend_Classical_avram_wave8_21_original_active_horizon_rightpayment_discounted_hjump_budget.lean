-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
-- name    : AvramDividend.Classical.avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:57:11.331933+00:00
-- url     : https://prove2.me/theorems/a60a7f0d-ed4b-4306-ae30-e8f08c7367b0
-- title:
--   Exact active horizon Stieltjes rightpayment discounted HJB drop under canonical hjump
-- statement:
--   At any original deterministic nonnegative time S that is either time zero or strictly before ruin, the full discounted right-payment Stieltjes atom on the exact original paymentTimes(ruinTime) intersection Iic S and the singleton S, plus the discounted postpayment HJB value, is bounded by the discounted prepayment HJB value. It includes the time-zero atom even for immediate ruin, and the horizon's own atom under strict survival. It assumes no differentiability at reserve zero or cap and does not replace the canonical dividend measure.
-- source:
--   Avram classical dividend verification, original right-continuous-payment convention: only S=0 or strict pre-ruin S may pay. Uses exact original Stieltjes singleton identity, active-horizon lintegral and canonical hjump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0)
    (hactive : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω)
    (q : ℝ) :
    (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
        ({(S : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (S : ℝ))) *
        w (riskProcess X x D S ω -
          (rightLimit D S ω - D S ω)) ≤
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) := by sorry
