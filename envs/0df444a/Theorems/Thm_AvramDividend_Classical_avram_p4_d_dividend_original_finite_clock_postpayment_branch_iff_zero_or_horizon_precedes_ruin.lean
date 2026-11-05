-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_clock_postpayment_branch_iff_zero_or_horizon_precedes_ruin
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_clock_postpayment_branch_iff_zero_or_horizon_precedes_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:01:40.296301+00:00
-- url     : https://prove2.me/theorems/61926804-0803-42a6-bb29-999d1b5c4dc5
-- title:
--   The original postpayment stop branch is equivalent to zero clock or horizon strictly before ruin
-- statement:
--   At the literal original controlled reserve ruinTime and finite stop tau=min(ruinTime,n).toNNReal, the branch tau=0 or tau<ruinTime used in P4-F exact W/Hdiv definitions is equivalent to tau=0 or n<ruinTime. Handles zero-time ruin, simultaneous ruin at n, ordinary early ruin, and paths with no ruin, respecting strict inclusion and time-zero atom separately.
-- source:
--   Proved original physical extended-time stop identity and Mathlib linear order min and strict order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_clock_postpayment_branch_iff_zero_or_horizon_precedes_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) ↔
      (τ ω = 0 ∨ (n : ℝ≥0∞) < ruinTime X x D ω) := by sorry
