-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:38:31.486922+00:00
-- url     : https://prove2.me/theorems/549251dc-d38e-4247-92ea-dde5705a482f
-- title:
--   Original paid stopped Stieltjes cash splits exactly into integrable surviving and positive-ruin event parts
-- statement:
--   For the exact P4-F original discounted Stieltjes Cash and random stopped clock, partition paths into τ=0 or τ<ruin and its complement. With a measurable event and assumed integrable Cash, both masked cash amounts remain integrable, and their sum is exactly Cash pathwise. The atom at time zero, admissible horizon right-payment and absence of a positive-ruin-time payment remain inside the unchanged original paymentTimes definition.
-- source:
--   Original Cash and paymentTimes/ruinTime definitions; Mathlib Integrable.indicator, Set.indicator_of_mem, Set.indicator_of_notMem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (s : Set Ω)
    (hs : s = {ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hsMeas : MeasurableSet s) :
    Integrable (s.indicator Cash) P ∧
    Integrable (sᶜ.indicator Cash) P ∧
    (∀ ω, Cash ω =
      s.indicator Cash ω + sᶜ.indicator Cash ω) := by sorry
