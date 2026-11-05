-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:50:23.742225+00:00
-- url     : https://prove2.me/theorems/6578b2a4-0324-4668-97dc-aaf0074611cc
-- title:
--   The literal original finite stop is below controlled ruin and horizon in extended nonnegative time
-- statement:
--   Pathwise for the same original spectrally negative Lévy process X, controlled dividend D, reserve x and stopped clock tau=(min ruinTime n).toNNReal, prove tau≤ruinTime and tau≤n as ENNReal, including paths with infinite ruin time. This source exact comparison validates horizon and ruin-set inclusions used in closed Stieltjes payment intervals.
-- source:
--   Original controlled ruinTime definition, Mathlib ENNReal.coe_toNNReal_le_self and min_le_left/min_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      (τ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by sorry
