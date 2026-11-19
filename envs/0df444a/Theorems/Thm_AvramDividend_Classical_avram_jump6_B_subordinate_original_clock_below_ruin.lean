-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_subordinate_original_clock_below_ruin
-- name    : AvramDividend.Classical.avram_jump6_B_subordinate_original_clock_below_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:25:39.04549+00:00
-- url     : https://prove2.me/theorems/d1ec911e-6ad9-4572-a463-8e76b32cc077
-- title:
--   Every subordinate original ruin-truncated clock lies before actual ruin
-- statement:
--   For the original Levy process, each clock sigma(k) dominated by the exact ruin-truncated NNReal clock tau is bounded above by original ruin time as an extended nonnegative real. This uses the existing Proved exact clock identity, with no path or finite-activity simplification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_subordinate_original_clock_below_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
