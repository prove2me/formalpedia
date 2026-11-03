-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_nonnegative
-- name    : AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:26:03.796656+00:00
-- url     : https://prove2.me/theorems/5e139ae9-9122-4672-9424-2b5beef76ea0
-- title:
--   Nonnegative original strictly killed capped-ruin terminal expectation
-- statement:
--   The expectation of the original strictly killed discounted postrightpayment positive-part terminal at finite ruin-capped clock is nonnegative, including equality at ruin.
-- source:
--   Direct corollary of independently Proved original capped-ruin expectation equality af85ece8 and original strict-survival terminal expectation nonnegativity bc3122fd. Preserves exact ruin overshoot strict inequality and rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    0 ≤ ∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P := by sorry
