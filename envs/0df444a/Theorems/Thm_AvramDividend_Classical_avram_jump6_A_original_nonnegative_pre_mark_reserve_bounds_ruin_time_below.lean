-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
-- name    : AvramDividend.Classical.avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:52:32.706654+00:00
-- url     : https://prove2.me/theorems/91cf3441-7b70-4783-b0e0-d1057301070b
-- title:
--   Original controlled reserve nonnegative before physical first mark bounds true ruin time below
-- statement:
--   For an actual original spectrally negative Lévy controlled risk process, if reserve is nonnegative at every physical clock t<σ, then the genuine ruinTime, defined as the infimum of clocks where reserve is negative, is at least σ. This exact original-source lower bound complements the already authored upper bound from a negative reserve at σ, jointly proving the equality of the original ruinTime with the physical first negative size-two Poisson arrival once the original pre- and at-mark path premises are supplied.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0)
    (hPre : ∀ t : ℝ≥0, t < σ → 0 ≤ riskProcess X x D t ω) :
    (σ : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
