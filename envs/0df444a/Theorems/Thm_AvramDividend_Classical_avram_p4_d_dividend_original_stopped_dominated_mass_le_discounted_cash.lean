-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:21:51.367563+00:00
-- url     : https://prove2.me/theorems/8c43cf59-7f94-475e-9232-3283ba281f27
-- title:
--   True original stopped paid submeasure mass controlled by exact discounted Cash at finite horizon
-- statement:
--   For the actual source right-continuous dividend Stieltjes measure, any physical dividend strategy D, sample path ω, original stopping clock σ, finite horizon T and nonnegative discount q, the exact discounted paymentTimes cash dominates exp(-qT) times the complete stopped mass of any path-dependent dividend submeasure ν≤dividendMeasure D ω. The closed paid clock includes its exact time-zero and horizon atoms and excludes positive ruin rightpayments by the source definition of paymentTimes. The inequality applies to singular-continuous as well as ordinary absolutely continuous dividend mass and is the correct finite-horizon source bridge from stopped ν mass to canonical Cash L1.
-- source:
--   Pinned Mathlib setLIntegral_const, lintegral_mono_ae, ENNReal.ofReal_le_ofReal and Real.exp_le_exp; original paymentTimes_measurable and paymentTimes_membership_to_nNReal_active. No density or absolute-continuity assumption, no stochastic law substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) *
      ν (paymentTimes σ ∩ Iic (T : ℝ)) ≤
      ∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) := by sorry
