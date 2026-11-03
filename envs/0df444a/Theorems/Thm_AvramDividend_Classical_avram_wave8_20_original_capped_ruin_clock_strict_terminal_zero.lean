-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_capped_ruin_clock_strict_terminal_zero
-- name    : AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_strict_terminal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:37:54.957094+00:00
-- url     : https://prove2.me/theorems/4f3c4efd-af31-4006-8b1e-4759c0eca3c6
-- title:
--   Original strict-survival postrightpayment terminal is exactly zero on the capped ruin branch
-- statement:
--   When actual ruin occurs at or before natural horizon n, the exact stopped physical-time source continuation payoff with strict ruin killing vanishes, including jump overshoot and creeping.
-- source:
--   At any realised ruinTime no later than finite n, the source capped clock (min(ruinTime,n)).toNNReal has exact coercion back to ruinTime; therefore the source strict-survival comparison is false and the entire discounted positive-part postrightpayment terminal is zero. Proof uses ENNReal.coe_toNNReal after proving the cap finite, preserving exact original stopping and overshoot semantics without BV stochastic drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_strict_terminal_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n : ℕ)
    (hRuin : ruinTime X x D ω ≤ (n : ℝ≥0∞)) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (if (τ : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ : ℝ))) *
        w (x + X.X τ ω - rightLimit D τ ω))
    else 0) = 0 := by sorry
