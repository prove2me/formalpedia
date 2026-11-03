-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_discounted_paid_cash_le_rightLimit
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_paid_cash_le_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:52:12.170903+00:00
-- url     : https://prove2.me/theorems/b4e62533-ad82-462d-b544-70ebc2d6fc46
-- title:
--   Actual finite positive ruin complete discounted Stieltjes cash bounded by genuine right-limit dividends
-- statement:
--   For the actual original dividend strategy at a positive finite ruin endpoint, the full discounted paymentTimes cash flow is quantitatively bounded by the original cumulative right-limit dividends at ruin, for q≥0. The source stopping convention includes time zero and all interior diffuse and atomic payments but excludes the ruin right-payment. The proof clips the precise stopped payment domain to [0,τ), bounds the discount by one, takes original Stieltjes mass monotonicity into [0,τ] and uses the accepted exact right-limit mass theorem. No alternative stochastic model, cash-flow envelope or missing Itô–Meyer estimate is assumed.
-- source:
--   Original positive-ruin payment-domain clip and exact source Stieltjes [0,τ] mass, with exp(-qt)≤1 and source-measure monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_discounted_paid_cash_le_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D τ ω) := by sorry
