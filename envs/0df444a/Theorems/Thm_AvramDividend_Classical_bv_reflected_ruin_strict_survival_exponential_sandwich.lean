-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_exponential_sandwich
-- name    : AvramDividend.Classical.bv_reflected_ruin_strict_survival_exponential_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:34:42.213994+00:00
-- url     : https://prove2.me/theorems/cae837e3-4971-4056-a548-33575e982aac
-- title:
--   Actual BV finite-activity strict zero-barrier survival lies between nearby first-jump exponential bounds
-- statement:
--   Combining the Proved actual-process upper bound for strict survival with the Proved first-negative-jump exponential lower bound for weak survival yields exp(-lambda(t+epsilon)) <= P(t<ruin) <= exp(-lambda*t) for each epsilon>0. The left inequality follows because survival through t+epsilon implies strict survival through t. This provides the exact two-sided quantitative approximation needed for passing to the time-continuity limit, with no assumption about atoms at fixed times.
-- source:
--   Avram, Palmowski and Pistorius (2007), zero-barrier finite-activity first-jump law following Proposition 1; Prove2Me already-Proved actual first-jump bounds.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_le_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_survival_ge_exp_first_jump
import Mathlib.MeasureTheory.Measure.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_reflected_ruin_strict_survival_exponential_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t ε : ℝ≥0) (hε : 0 < ε) :
    Real.exp (-((((t + ε : ℝ≥0) : ℝ) *
      (X.ν (Iio (0 : ℝ))).toReal))) ≤
        P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ∧
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ≤
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
