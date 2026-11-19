-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
-- name    : AvramDividend.Classical.avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T21:01:58.325207+00:00
-- url     : https://prove2.me/theorems/1c983d3d-abbb-4b94-a0a3-7f40d6d43607
-- title:
--   All original stopped physical clocks are bounded by the exact integer ruin-truncation horizon
-- statement:
--   For the actual spectrally negative Levy reserve with original horizon tau=min(ruinTime,n), any family of stopping times sigma(k) dominated by tau is bounded pathwise by the real NNReal horizon n. This discharges the exact required hTauBound hypothesis in the already Proved canonical strict-pre-ruin original closed-Iic cash Stieltjes grid theorem, for every k and omega. No finite jump-activity assumption, no surrogate clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, σ k ω ≤ (n : ℝ≥0) := by sorry
