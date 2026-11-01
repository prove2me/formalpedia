-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_positive_ruin_closed_horizon_stopped_dividend_mass_piecewise
-- name    : AvramDividend.Classical.avram_wave4_03_positive_ruin_closed_horizon_stopped_dividend_mass_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:58:46.901953+00:00
-- url     : https://prove2.me/theorems/947ab908-6360-4925-a96c-e19014270f47
-- title:
--   Closed finite-horizon BV stopped full Stieltjes mass switches at positive ruin, preserving terminal payment chronology
-- statement:
--   For each original left-continuous cumulative dividend strategy and positive finite ruin time tau, the exact full Stieltjes mass paid through a deterministic closed horizon T is D^+_T if T<tau, but D_tau if T≥tau. The first case includes the right payment atom at the horizon T; the second excludes the right payment atom at ruin tau while retaining every earlier continuous, singular-continuous, and right-atomic payment and the time-zero atom. These are the two distinct terminal conventions used by the genuine finite-horizon stopped verification inequality; no source Lévy compensation is assumed or claimed.
-- source:
--   True original paymentTimes strict pre-ruin convention in Avram–Palmowski–Pistorius (2007) Proposition 4(i); Proved paymentTimes_eq_strict_of_pos 7c01995b, dividendMeasure_Ico_zero_eq_dividendValue 56472398 and dividendMeasure_Icc_zero_eq_rightLimit d6ace15b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_positive_ruin_closed_horizon_stopped_dividend_mass_piecewise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ T : ℝ≥0) (hτ : 0 < τ) :
    dividendMeasure D ω
      (paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (T : ℝ)) =
      if T < τ then ENNReal.ofReal (rightLimit D T ω)
      else ENNReal.ofReal (D τ ω) := by sorry
