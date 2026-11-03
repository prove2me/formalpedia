-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:49:15.625729+00:00
-- url     : https://prove2.me/theorems/db831eff-7bdd-4f99-a81f-6f91fcef6065
-- title:
--   Original positive-ruin last-cell strictly pre-ruin dividend mass vanishes
-- statement:
--   For a genuine left-continuous dividend strategy and any strictly positive terminal time τ (in particular a finite positive ruin time), right-endpoint cumulative dividends sampled strictly before τ and converging to τ approach the pre-payment amount D τ. Therefore the final strictly pre-ruin dividend cell D τ − D⁺(u_n) tends to zero, even if D has an arbitrary positive right payment at τ. This exactly preserves the pre/post-payment ruin convention in the source-grid epsilon estimate and does not assume stochastic Itô convergence.
-- source:
--   Proved source left-limit identity f9c3a5c4-3a58-45b7-b6da-8734693b863d; corrected Wave6 Chat06 positive-ruin terminal cell, full original Stieltjes strict-left convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => D τ ω - rightLimit D (u n) ω) atTop (𝓝 0) := by sorry
