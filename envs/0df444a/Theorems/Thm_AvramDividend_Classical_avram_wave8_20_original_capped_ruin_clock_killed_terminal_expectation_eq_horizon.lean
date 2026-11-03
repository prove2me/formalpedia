-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
-- name    : AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:49:07.081934+00:00
-- url     : https://prove2.me/theorems/af85ece8-2fba-4b26-bdb4-3735a3d4dfc8
-- title:
--   Original stopped-at-ruin killed terminal expectation equals deterministic-horizon expectation
-- statement:
--   The expected exact strictly surviving discounted post-rightpayment candidate terminal evaluated at the finite min(ruinTime,n) clock is equal to its deterministic-horizon counterpart for each original sample and law. Includes zero-at-ruin boundary and overshoot.
-- source:
--   Original source finite capped ruin stopped clock. Uses the independently remotely Proved W8-20 pathwise exact stopped-terminal equality ce831291 to transport it under the original probability measure with integral_congr_ae. No integrability or supermartingale premise is inserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_killed_terminal_expectation_eq_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∫ ω, (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) ∂P) =
    (∫ ω, (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
      else 0) ∂P) := by sorry
