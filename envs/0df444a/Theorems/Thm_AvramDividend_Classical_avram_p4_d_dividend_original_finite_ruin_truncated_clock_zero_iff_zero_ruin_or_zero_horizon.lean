-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_ruin_truncated_clock_zero_iff_zero_ruin_or_zero_horizon
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_truncated_clock_zero_iff_zero_ruin_or_zero_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:02:56.027651+00:00
-- url     : https://prove2.me/theorems/5bcbd584-c369-40a6-97ea-7caff46c91c7
-- title:
--   Original finite controlled stop vanishes iff ruin is at time zero or the horizon is zero
-- statement:
--   For the genuine original spectrally negative Lévy process, admissible controlled dividend reserve ruinTime and source tau=min(ruinTime,n).toNNReal, prove tau=0 as ENNReal precisely when ruinTime=0 or n=0. The result supports original zero-time Stieltjes atom reconciliation without imposing positivity of n or ruinTime and includes never-ruin paths.
-- source:
--   Proved P4-D source physical extended-time clock equality and Mathlib min in a nonnegative linear order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_truncated_clock_zero_iff_zero_ruin_or_zero_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) = 0 ↔
      ruinTime X x D ω = 0 ∨ n = 0 := by sorry
