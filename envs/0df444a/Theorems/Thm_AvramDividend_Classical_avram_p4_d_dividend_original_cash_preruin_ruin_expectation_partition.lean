-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_cash_preruin_ruin_expectation_partition
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_expectation_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:49:58.606583+00:00
-- url     : https://prove2.me/theorems/1751a961-f72b-4dbf-b03b-4120e908ead7
-- title:
--   Original expected stopped dividend cash is exactly the sum of nonnegative surviving and positive-ruin event rewards
-- statement:
--   The genuine original full paid discounted Stieltjes Cash is integrable and nonnegative on every path. At the measurable survival or initial-stopping event, the expected total cash splits exactly into two nonnegative expectations for the survival and stopped-at-ruin alternatives. This transports the exact atom-preserving pathwise partition into the Proposition 4(i) expected reward budget, without inventing a terminal payment or altering the original event convention.
-- source:
--   Proved P4-D original random cash L1 event partition UUID 549251dc-d38e-4247-92ea-dde5705a482f and proved P4-F original stopped cash nonneg UUID 4db282c6-0692-4c9b-b797-eda5920defa4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_expectation_partition
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
    (∫ ω, Cash ω ∂P) =
      (∫ ω, s.indicator Cash ω ∂P) +
      (∫ ω, sᶜ.indicator Cash ω ∂P) ∧
    0 ≤ (∫ ω, s.indicator Cash ω ∂P) ∧
    0 ≤ (∫ ω, sᶜ.indicator Cash ω ∂P) := by sorry
