-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:16:11.907455+00:00
-- url     : https://prove2.me/theorems/19babd50-3394-4e92-9fca-45199d1cbc35
-- title:
--   Exact original strictly killed terminal converges to zero along every post-ruin right-clock sequence
-- statement:
--   For every sample path at or after actual ruin, the exactly killed post-rightpayment terminal is zero at all later clocks, so every sequence of clocks to the right has zero limit. This handles zero landing, creeping and overshoot without incorrectly requiring strict reserve negativity at ruin.
-- source:
--   Source exact strict ruinTime and postrightpayment positive HJB terminal. Accepted W8-20 c07eabc1 shows it vanishes identically for each physical clock after an already ruined t. Thus any sequence of clocks at or after t has identically zero terminal and converges to zero regardless of clock convergence or adverse overshoot. No supermartingale assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hRuin : ruinTime X x D ω ≤ (t : ℝ≥0∞))
    (τ : ℕ → ℝ≥0) (hRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop (𝓝 (0 : ℝ)) := by sorry
