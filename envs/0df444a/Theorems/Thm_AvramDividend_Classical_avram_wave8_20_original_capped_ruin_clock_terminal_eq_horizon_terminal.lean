-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
-- name    : AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:50:30.435111+00:00
-- url     : https://prove2.me/theorems/ce831291-9200-4a46-875b-bbc971e5b912
-- title:
--   Exact original killed terminal at capped ruin stopping clock equals deterministic-horizon killed terminal pathwise
-- statement:
--   For each physical sample path and finite natural horizon, the exact strict-survival killed postrightpayment terminal evaluated at the genuine capped ruin clock equals the same killed terminal at the deterministic horizon. This is an exact boundary relation including overshoot and time-zero ruin.
-- source:
--   On each original sample path, min(ruinTime,n) equals actual ruin if ruin≤n and equals n when strict survival beyond n. The exact source killed postrightpayment continuation is zero in the first branch and is the deterministic-n continuation in the second. Prove the NNReal-to-ENNReal clock conversion at finite min with pinned coe_toNNReal, and cast n consistently. No stochastic expectation, generator or extra assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (if (τ : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ : ℝ))) *
        w (x + X.X τ ω - rightLimit D τ ω))
    else 0) =
    (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
    else 0) := by sorry
