-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
-- name    : AvramDividend.Classical.avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:44:40.253202+00:00
-- url     : https://prove2.me/theorems/f77d306f-d341-4248-a099-ade5440d5676
-- title:
--   Actual strict survival is eventually preserved along source physical-time clocks converging to an interior time
-- statement:
--   At a source sample path and any strictly pre-ruin physical time t, every sequence of physical times converging to t is eventually strictly before ruin. This supplies the exact eventual branch of the strict-survival if in limit arguments; separately verify the post-rightpayment payoff right-continuity for terminal convergence.
-- source:
--   Original controlled ruinTime, physical time and strict survival. The strictly pre-ruin set is open as a continuous preimage of the ENNReal order Iio. A clock converging to a strictly surviving physical time therefore eventually lies on the strict surviving side. Handles exact source jump and creeping boundaries without a false claim that clock convergence alone implies payoff continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t)) :
    ∀ᶠ n in Filter.atTop, (τ n : ℝ≥0∞) < ruinTime X x D ω := by sorry
